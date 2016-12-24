{-# LANGUAGE TypeFamilies, DeriveFunctor #-}
module Test.QuickCheck.Counterexamples(module Test.QuickCheck.Counterexamples, module Test.QuickCheck) where

import Data.IORef
import Test.QuickCheck hiding
  ( quickCheck, quickCheckWith, quickCheckResult, quickCheckWithResult
  , verboseCheck, verboseCheckWith, verboseCheckResult, verboseCheckWithResult
  , Property, Testable(..)
  , forAll
  , forAllShrink
  , shrinking
  , (==>)
  , (===)
  , ioProperty
  , verbose
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
  , Discard(..)
  , discard
  , mapSize
  )
import qualified Test.QuickCheck as QC

newtype Property cex = Property { unProperty :: (cex -> IO ()) -> QC.Property }
  deriving Functor

class QC.Testable prop => Testable prop where
  type Counterexample prop
  property :: prop -> Property (Counterexample prop)

instance Testable Bool where
  type Counterexample Bool = ()
  property prop = Property (\f -> QC.whenFail (f ()) prop)

instance Testable QC.Property where
  type Counterexample QC.Property = ()
  property prop = Property (\f -> QC.whenFail (f ()) prop)

instance QC.Testable (Property cex) where
  property prop = unProperty prop (\_ -> return ())

instance Testable (Property cex) where
  type Counterexample (Property cex) = cex
  property = id

instance (Show a, QC.Arbitrary a, Testable b) => Testable (a -> b) where
  type Counterexample (a -> b) = (a, Counterexample b)
  property prop = forAllShrink arbitrary shrink prop

forAllShrink :: (Testable prop, Show a) => Gen a -> (a -> [a]) -> (a -> prop) -> Property (a, Counterexample prop)
forAllShrink arb shr prop =
  Property $ \f ->
    QC.forAllShrink arb shr $ \x ->
      unProperty (property (prop x)) (\y -> f (x, y))

onProperty :: Testable prop => (QC.Property -> QC.Property) -> prop -> Property (Counterexample prop)
onProperty f prop =
  Property (\k -> f (unProperty (property prop) k))

(==>) :: Testable prop => Bool -> prop -> Property (Counterexample prop)
x ==> prop = onProperty (x QC.==>) prop

(===) :: (Eq a, Show a) => a -> a -> Property ()
x === y = property (x QC.=== y)

quickCheck :: Testable prop => prop -> IO (Maybe (Counterexample prop))
quickCheck prop = do
  ref <- newIORef (error "counterexample not available")
  res <- QC.quickCheckResult (unProperty (property prop) (writeIORef ref))
  case res of
    Failure{} ->
      fmap Just (readIORef ref)
    _ -> return Nothing
