module Kore.MatchingLogic.DummyProofSystem
    ( DummyRule(DummyRule)
    , DummyError(..)
    ) where
import           Data.Text

import           Kore.MatchingLogic.HilbertProof

newtype DummyRule formula = DummyRule Text
data DummyError = DummyError
instance Show (DummyRule formula) where
    show (DummyRule rule) = unpack rule

instance (Eq formula)
    => ProofSystem DummyError (DummyRule formula) formula
  where
    checkDerivation _ _ _ = return ()
