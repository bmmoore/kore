module Kore.MatchingLogic.MLProofSystem where

import           Data.Kore.AST.Common            (Meta, Variable)
import           Data.Kore.AST.Kore

import           Kore.MatchingLogic.Error
import           Kore.MatchingLogic.HilbertProof

type Var = Variable Meta
type Symbol = ()

data MLRule index =
   Propositional1 index index
 | Propositional2 index index index
 | Propositional3 index index
 | ModusPonens index index
 | Generalization Var index -- Var ix
 | VariableSubstitution Var Var index
 | Forall Var index index
 | Necessitation Symbol Int index --Symbol Int ix
 | PropagateOr Symbol Int index index
     -- ^ sigma(before ..,\phi1 \/ \phi2,.. after) <->
     --     sigma(before ..,\phi1, .. after) <-> sigma(before ..,\phi2,.. after)
 | PropagateExists Symbol Int Var index
     -- ^ sigma(before ..,Ex x. phi,.. after) <-> Ex x.sigma(before ..,phi,.. after)
 | Existence Var
     -- ^ Ex x.x
 | Singvar Var index [Int] [Int]

instance (Show index, Eq index)
    => ProofSystem (MLRule index) UnifiedPattern where
  checkDerivation _ _ _ = mlSuccess
