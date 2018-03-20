module Kore.MatchingLogic.MLProofSystem where

import           Data.Kore.AST.Common            (Meta, Variable)
import           Data.Kore.AST.Kore              (UnifiedPattern)

import           Kore.MatchingLogic.Error
import           Kore.MatchingLogic.HilbertProof

type Var = Variable Meta
type Symbol = ()

data MLRule index =
   Propositional1 UnifiedPattern UnifiedPattern
 | Propositional2 UnifiedPattern UnifiedPattern UnifiedPattern
 | Propositional3 UnifiedPattern UnifiedPattern
 | ModusPonens index index
 | Generalization Var index -- Var ix
 | VariableSubstitution Var Var UnifiedPattern
 | Forall Var UnifiedPattern UnifiedPattern
 | Necessitation Symbol Int index --Symbol Int ix
 | PropagateOr Symbol Int UnifiedPattern UnifiedPattern
     -- ^ sigma(before ..,\phi1 \/ \phi2,.. after) <->
     --     sigma(before ..,\phi1, .. after) <-> sigma(before ..,\phi2,.. after)
 | PropagateExists Symbol Int Var UnifiedPattern
     -- ^ sigma(before ..,Ex x. phi,.. after) <-> Ex x.sigma(before ..,phi,.. after)
 | Existence Var
     -- ^ Ex x.x
 | Singvar Var UnifiedPattern [Int] [Int]

instance (Show index, Eq index)
    => ProofSystem (MLRule index) UnifiedPattern where
  checkDerivation _ _ _ = mlSuccess
