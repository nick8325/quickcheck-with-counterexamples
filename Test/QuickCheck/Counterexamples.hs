{-|
This module extends QuickCheck so that it returns counterexamples
as Haskell values instead of just printing them. To use it, import
this module /instead of/ "Test.QuickCheck". The API and functionality
are the same as normal QuickCheck; the only difference is that the
return types of 'quickCheck' (and related functions)
include a counterexample.

Note that this module re-exports most functions from
"Test.QuickCheck". Those functions are /not/ documented here! You will
need to refer to the main "Test.QuickCheck" documentation when using
this module.

Here is an example of getting counterexamples.
Suppose we have the following property:

@
prop_reverse_append :: [Int] -> [Int] -> Property
prop_reverse_append xs ys =
  reverse (xs++ys) === reverse xs ++ reverse ys
@

If we look the type of @quickCheck prop_reverse_append@, we see that
it returns a counterexample:

>>> :t quickCheck prop_reverse_append
quickCheck prop_reverse_append :: IO (Maybe ([Int] :&: [Int] :&: ()))

The 'Maybe' is there because 'quickCheck' will return 'Nothing' if the
property succeeds; ':&:' is a datatype of pairs.

If we run QuickCheck, we can get the counterexample as a normal
Haskell value:

>>> Just (xs :&: ys :&: ()) <- quickCheck prop_reverse_append
*** Failed! Falsifiable (after 5 tests and 4 shrinks):
[0]
[1]
[1,0] /= [0,1]

>>> :t xs
xs :: [Int]

>>> xs
[0]

>>> ys
[1]

If you use 'counterexample' in your property, the string you pass
won't be returned as a Haskell value. You might instead want to use
'typedCounterexample', which adds a Haskell value to the counterexample
(but doesn't print it).

That ought to be all you need to know to use this module. If you want all
the details, here is how this module alters QuickCheck's API:

* There is a new type @'PropertyOf' cex@, which represents a property that
  (if it fails) generates a counterexample of type @cex@. 'Property' is now
  a synonym for @'PropertyOf' ()@. The 'Testable' class now has an associated
  type 'Counterexample' which describes the counterexample.
* The QuickCheck property combinators take and return 'PropertyOf' instead of
  'Property' wherever possible, in order to preserve the counterexample.
* 'quickCheck' and related functions return a @'Counterexample' prop@.
* There are two new combinators 'typedCounterexample' and 'onProperty'.
-}

{-# LANGUAGE TypeOperators, TypeFamilies, DeriveFunctor, TemplateHaskell #-}
module Test.QuickCheck.Counterexamples(module Test.QuickCheck.Counterexamples, module Test.QuickCheck) where

import Data.IORef
import Test.QuickCheck hiding
  ( quickCheck, quickCheckWith, quickCheckResult, quickCheckWithResult
  , verboseCheck, verboseCheckWith, verboseCheckResult, verboseCheckWithResult
  , labelledExamples, labelledExamplesWith, labelledExamplesResult, labelledExamplesWithResult
  , polyQuickCheck, polyVerboseCheck
  , Property, Testable(..)
  , forAll
  , forAllShrink
  , forAllShow
  , forAllShrinkShow
  , forAllBlind
  , forAllShrinkBlind
  , shrinking
  , (==>)
  , (===)
  , (=/=)
  , ioProperty
  , idempotentIOProperty
  , verbose
  , verboseShrinking
  , once
  , again
  , within
  , noShrinking
  , (.&.)
  , (.&&.)
  , conjoin
  , (.||.)
  , disjoin
  , counterexample
  , printTestCase
  , whenFail
  , whenFail'
  , expectFailure
  , label
  , collect
  , classify
  , cover
  , tabulate
  , coverTable
  , checkCoverage
  , checkCoverageWith
  , mapSize
  )
import qualified Test.QuickCheck as QC
import Language.Haskell.TH
import Control.Monad

-- * The 'PropertyOf' type and 'Testable' typeclass

-- | A property. @cex@ is the type of counterexamples to the property.
--
-- Note that there is a 'Functor' instance, which is useful when you
-- want to manipulate the counterexample, e.g., to change its type.
-- For example, when some branches of your property produce a
-- counterexample and other branches do not, the types will not match
-- up, but using 'fmap' you can make the counterexample be a 'Maybe'.

newtype PropertyOf cex =
  MkProperty {
    -- | Implementation note: the property receives a callback
    -- to which it should pass the counterexample after shrinking.
    unProperty :: (cex -> IO ()) -> QC.Property }
  deriving Functor

-- | A property which doesn't produce a counterexample.
type Property = PropertyOf ()

-- | A type synonym for the property which comes from a particular 'Testable' instance.
type PropertyFrom prop = PropertyOf (Counterexample prop)

-- | The class of properties, i.e. types which QuickCheck knows how to test.
class QC.Testable prop => Testable prop where
  -- | The type of counterexamples to the property.
  type Counterexample prop
  -- | Convert the property to a 'PropertyOf'.
  property :: prop -> PropertyFrom prop

  -- | See 'Test.QuickCheck.propertyForAllShrinkShow'.
  propertyForAllShrinkShow :: Show a => Gen a -> (a -> [a]) -> (a -> String) -> (a -> prop) -> PropertyOf (a :&: Counterexample prop)
  propertyForAllShrinkShow gen shr f =
    forAllShrinkShow gen shr f

instance Testable Discard where
  type Counterexample Discard = ()
  property prop = MkProperty (\_ -> QC.property prop)

instance Testable () where
  type Counterexample () = ()
  property prop = MkProperty (\f -> QC.whenFail (f ()) prop)

instance Testable prop => Testable (Maybe prop) where
  type Counterexample (Maybe prop) = Counterexample prop
  property = property . liftMaybe
    where
      -- See comment for liftUnit above
      liftMaybe prop@Nothing = MkProperty (\_ -> QC.property prop)
      liftMaybe (Just prop) = property prop

instance Testable Bool where
  type Counterexample Bool = ()
  property prop = MkProperty (\f -> QC.whenFail (f ()) prop)

instance Testable QC.Property where
  type Counterexample QC.Property = ()
  property prop = MkProperty (\f -> QC.whenFail (f ()) prop)

instance Testable prop => Testable (Gen prop) where
  type Counterexample (Gen prop) = Counterexample prop
  property prop = MkProperty $ \k ->
    -- prop :: Gen prop
    -- unProperty . property <$> prop ::
    --   Gen ((cex -> IO ()) -> Property)
    -- unProperty . property <$> prop <*> pure k ::
    --   Gen Property
    QC.property (unProperty . property <$> prop <*> pure k)

instance QC.Testable (PropertyOf cex) where
  property prop = unProperty prop (\_ -> return ())

instance Testable (PropertyOf cex) where
  type Counterexample (PropertyOf cex) = cex
  property = id

instance (Show a, QC.Arbitrary a, Testable b) => Testable (a -> b) where
  type Counterexample (a -> b) = a :&: Counterexample b
  property prop = propertyForAllShrinkShow arbitrary shrink show prop

  -- Copied from QuickCheck
  propertyForAllShrinkShow gen shr shw f =
    -- gen :: Gen b, shr :: b -> [b], f :: b -> a -> prop
    -- Idea: Generate and shrink (b, a) as a pair
    fmap (\((x, y) :&: z) -> x :&: y :&: z) $
    propertyForAllShrinkShow
      (liftM2 (,) gen arbitrary)
      (liftShrink2 shr shrink)
      (\(x, y) -> shw x ++ "\n" ++ show y)
      (uncurry f)

-- * New functionality which is not in QuickCheck

-- | A type of pairs. Used in counterexamples.
infixr 6 :&:
data a :&: b = a :&: b deriving (Eq, Ord, Show, Read)

-- | Add a value to the counterexample.
-- The value is not printed as part of the counterexample;
-- if you want it to be, use 'counterexample' as well.
typedCounterexample :: Testable prop => a -> prop -> PropertyOf (a :&: Counterexample prop)
typedCounterexample x prop = fmap (x :&:) (property prop)

-- | Lift an ordinary QuickCheck property combinator to one with counterexamples.
onProperty :: Testable prop => (QC.Property -> QC.Property) -> prop -> PropertyFrom prop
onProperty f prop =
  MkProperty (\k -> f (unProperty (property prop) k))

-- * The standard QuickCheck combinators, updated to return counterexamples

-- | See 'Test.QuickCheck.quickCheck' in "Test.QuickCheck".
quickCheck :: Testable prop => prop -> IO (Maybe (Counterexample prop))
quickCheck = quickCheckWith stdArgs

-- | See 'Test.QuickCheck.quickCheckWith' in "Test.QuickCheck".
quickCheckWith :: Testable prop => Args -> prop -> IO (Maybe (Counterexample prop))
quickCheckWith args prop = fmap fst (quickCheckWithResult args prop)

-- | See 'Test.QuickCheck.quickCheckResult' in "Test.QuickCheck".
quickCheckResult :: Testable prop => prop -> IO (Maybe (Counterexample prop), Result)
quickCheckResult = quickCheckWithResult stdArgs

-- | See 'Test.QuickCheck.quickCheckWithResult' in "Test.QuickCheck".
quickCheckWithResult :: Testable prop => Args -> prop -> IO (Maybe (Counterexample prop), Result)
quickCheckWithResult args prop = do
  ref <- newIORef Nothing
  let
    -- Because the Testable instances for Bool and Property use whenFail,
    -- this function will only be called once, at the end of shrinking.
    modify x Nothing = Just x
    modify _ (Just _) =
      error "Internal error in quickcheck-with-counterexamples: IORef written to twice"
  res <- QC.quickCheckWithResult args $
    unProperty (property prop) (modifyIORef ref . modify)
  cex <- readIORef ref
  return (cex, res)

-- | See 'Test.QuickCheck.verboseCheck' in "Test.QuickCheck".
verboseCheck :: Testable prop => prop -> IO (Maybe (Counterexample prop))
verboseCheck p = quickCheck (verbose p)

-- | See 'Test.QuickCheck.verboseCheckWith' in "Test.QuickCheck".
verboseCheckWith :: Testable prop => Args -> prop -> IO (Maybe (Counterexample prop))
verboseCheckWith args p = quickCheckWith args (verbose p)

-- | See 'Test.QuickCheck.verboseCheckResult' in "Test.QuickCheck".
verboseCheckResult :: Testable prop => prop -> IO (Maybe (Counterexample prop), Result)
verboseCheckResult p = quickCheckResult (verbose p)

-- | See 'Test.QuickCheck.verboseCheckWithResult' in "Test.QuickCheck".
verboseCheckWithResult :: Testable prop => Args -> prop -> IO (Maybe (Counterexample prop), Result)
verboseCheckWithResult a p = quickCheckWithResult a (verbose p)

-- | See 'Test.QuickCheck.labelledExamples' in "Test.QuickCheck".
labelledExamples :: Testable prop => prop -> IO (Maybe (Counterexample prop))
labelledExamples p = quickCheck (verbose p)

-- | See 'Test.QuickCheck.labelledExamplesWith' in "Test.QuickCheck".
labelledExamplesWith :: Testable prop => Args -> prop -> IO (Maybe (Counterexample prop))
labelledExamplesWith args p = quickCheckWith args (verbose p)

-- | See 'Test.QuickCheck.labelledExamplesResult' in "Test.QuickCheck".
labelledExamplesResult :: Testable prop => prop -> IO (Maybe (Counterexample prop), Result)
labelledExamplesResult p = quickCheckResult (verbose p)

-- | See 'Test.QuickCheck.labelledExamplesWithResult' in "Test.QuickCheck".
labelledExamplesWithResult :: Testable prop => Args -> prop -> IO (Maybe (Counterexample prop), Result)
labelledExamplesWithResult a p = quickCheckWithResult a (verbose p)

-- | See 'Test.QuickCheck.polyQuickCheck' in "Test.QuickCheck".
polyQuickCheck :: Name -> ExpQ
polyQuickCheck x = [| quickCheck $(monomorphic x) |]

-- | See 'Test.QuickCheck.polyVerboseCheck' in "Test.QuickCheck".
polyVerboseCheck :: Name -> ExpQ
polyVerboseCheck x = [| verboseCheck $(monomorphic x) |]

-- | See 'Test.QuickCheck.forAll' in "Test.QuickCheck".
forAll :: (Testable prop, Show a) => Gen a -> (a -> prop) -> PropertyOf (a :&: Counterexample prop)
forAll arb prop = forAllShrink arb shrinkNothing prop

-- | See 'Test.QuickCheck.forAllShrink' in "Test.QuickCheck".
forAllShrink :: (Testable prop, Show a) => Gen a -> (a -> [a]) -> (a -> prop) -> PropertyOf (a :&: Counterexample prop)
forAllShrink arb shr prop =
  forAllShrinkShow arb shr show prop

-- | See 'Test.QuickCheck.forAllShow' in "Test.QuickCheck".
forAllShow :: Testable prop => Gen a -> (a -> String) -> (a -> prop) -> PropertyOf (a :&: Counterexample prop)
forAllShow arb shw prop = forAllShrinkShow arb shrinkNothing shw prop

-- | See 'Test.QuickCheck.forAllShrinkShow' in "Test.QuickCheck".
forAllShrinkShow :: Testable prop => Gen a -> (a -> [a]) -> (a -> String) -> (a -> prop) -> PropertyOf (a :&: Counterexample prop)
forAllShrinkShow arb shr shw prop =
  forAllShrinkBlind arb shr (\x -> counterexample (shw x) (prop x))

-- | See 'Test.QuickCheck.forAllBlind' in "Test.QuickCheck".
forAllBlind :: Testable prop => Gen a -> (a -> prop) -> PropertyOf (a :&: Counterexample prop)
forAllBlind arb prop = forAllShrinkBlind arb shrinkNothing prop

-- | See 'Test.QuickCheck.forAllShrinkBlind' in "Test.QuickCheck".
forAllShrinkBlind :: Testable prop => Gen a -> (a -> [a]) -> (a -> prop) -> PropertyOf (a :&: Counterexample prop)
forAllShrinkBlind arb shr prop =
  MkProperty $ \f ->
    QC.forAllShrinkBlind arb shr $ \x ->
      unProperty (property (prop x)) (\y -> f (x :&: y))

-- | See 'Test.QuickCheck.shrinking' in "Test.QuickCheck".
shrinking :: Testable prop => (a -> [a]) -> a -> (a -> prop) -> PropertyFrom prop
shrinking shr x prop =
  MkProperty $ \k -> QC.shrinking shr x $ \x ->
    unProperty (property (prop x)) k

-- | See 'Test.QuickCheck.==>' in "Test.QuickCheck".
infixr 0 ==>
(==>) :: Testable prop => Bool -> prop -> PropertyFrom prop
x ==> prop = onProperty (x QC.==>) prop

-- | See 'Test.QuickCheck.===' in "Test.QuickCheck".
infix 4 ===
(===) :: (Eq a, Show a) => a -> a -> Property
x === y = property (x QC.=== y)

-- | See 'Test.QuickCheck.=/=' in "Test.QuickCheck".
infix 4 =/=
(=/=) :: (Eq a, Show a) => a -> a -> Property
x =/= y = property (x QC.=/= y)

-- | See 'Test.QuickCheck.ioProperty' in "Test.QuickCheck".
ioProperty :: Testable prop => IO prop -> PropertyFrom prop
ioProperty ioprop =
  MkProperty $ \k -> QC.ioProperty $ do
    prop <- ioprop
    return (unProperty (property prop) k)

-- | See 'Test.QuickCheck.idempotentIOProperty' in "Test.QuickCheck".
idempotentIOProperty :: Testable prop => IO prop -> PropertyFrom prop
idempotentIOProperty ioprop =
  MkProperty $ \k -> QC.idempotentIOProperty $ do
    prop <- ioprop
    return (unProperty (property prop) k)

-- | See 'Test.QuickCheck.verbose' in "Test.QuickCheck".
verbose :: Testable prop => prop -> PropertyFrom prop
verbose = onProperty QC.verbose

-- | See 'Test.QuickCheck.verboseShrinking' in "Test.QuickCheck".
verboseShrinking :: Testable prop => prop -> PropertyFrom prop
verboseShrinking = onProperty QC.verboseShrinking

-- | See 'Test.QuickCheck.once' in "Test.QuickCheck".
once :: Testable prop => prop -> PropertyFrom prop
once = onProperty QC.once

-- | See 'Test.QuickCheck.again' in "Test.QuickCheck".
again :: Testable prop => prop -> PropertyFrom prop
again = onProperty QC.again

-- | See 'Test.QuickCheck.within' in "Test.QuickCheck".
within :: Testable prop => Int -> prop -> PropertyFrom prop
within n = onProperty (QC.within n)

-- | See 'Test.QuickCheck.noShrinking' in "Test.QuickCheck".
noShrinking :: Testable prop => prop -> PropertyFrom prop
noShrinking = onProperty QC.noShrinking

-- | See 'Test.QuickCheck.counterexample' in "Test.QuickCheck".
counterexample :: Testable prop => String -> prop -> PropertyFrom prop
counterexample msg = onProperty (QC.counterexample msg)

-- | See 'Test.QuickCheck.whenFail' in "Test.QuickCheck".
whenFail :: Testable prop => IO () -> prop -> PropertyFrom prop
whenFail m = onProperty (QC.whenFail m)

-- | See 'Test.QuickCheck.whenFail'' in "Test.QuickCheck".
whenFail' :: Testable prop => IO () -> prop -> PropertyFrom prop
whenFail' m = onProperty (QC.whenFail' m)

-- | See 'Test.QuickCheck.expectFailure' in "Test.QuickCheck".
expectFailure :: Testable prop => prop -> PropertyFrom prop
expectFailure = onProperty QC.expectFailure

-- | See 'Test.QuickCheck.label' in "Test.QuickCheck".
label :: Testable prop => String -> prop -> PropertyFrom prop
label lab = onProperty (QC.label lab)

-- | See 'Test.QuickCheck.collect' in "Test.QuickCheck".
collect :: (Show a, Testable prop) => a -> prop -> PropertyFrom prop
collect x = onProperty (QC.collect x)

-- | See 'Test.QuickCheck.classify' in "Test.QuickCheck".
classify :: Testable prop => Bool -> String -> prop -> PropertyFrom prop
classify cond lab = onProperty (QC.classify cond lab)

-- | See 'Test.QuickCheck.cover' in "Test.QuickCheck".
cover :: Testable prop => Double -> Bool -> String -> prop -> PropertyFrom prop
cover percent cond lab = onProperty (QC.cover percent cond lab)

-- | See 'Test.QuickCheck.tabulate' in "Test.QuickCheck".
tabulate :: Testable prop => String -> [String] -> prop -> PropertyFrom prop
tabulate table values = onProperty (QC.tabulate table values)

-- | See 'Test.QuickCheck.coverTables' in "Test.QuickCheck".
coverTables :: Testable prop => String -> [(String, Double)] -> prop -> PropertyFrom prop
coverTables table percents = onProperty (QC.coverTable table percents)

-- | See 'Test.QuickCheck.checkCoverage' in "Test.QuickCheck".
checkCoverage :: Testable prop => prop -> PropertyFrom prop
checkCoverage = onProperty QC.checkCoverage

-- | See 'Test.QuickCheck.checkCoverageWith' in "Test.QuickCheck".
checkCoverageWith :: Testable prop => Confidence -> prop -> PropertyFrom prop
checkCoverageWith confidence = onProperty (QC.checkCoverageWith confidence)

-- | See 'Test.QuickCheck.mapSize' in "Test.QuickCheck".
mapSize :: Testable prop => (Int -> Int) -> prop -> PropertyFrom prop
mapSize f = onProperty (QC.mapSize f)
