{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Kore.MatchingLogic.HilbertProof
  (Proof(index,claims,derivations)
  ,ProofSystem(..)
  ,emptyProof
  ,add
  ,derive
  ,renderProof
  )   where
import           Data.Foldable
import           Data.Map.Strict          (Map)
import qualified Data.Map.Strict          as Map
import           Data.Sequence            (Seq, (|>))
import qualified Data.Sequence            as Seq

import           Data.Kore.Error

import           Kore.MatchingLogic.Error

data Proof ix rule formula =
  Proof
  { index       :: Map ix (Int,formula)
  , claims      :: Seq (ix,formula)
  , derivations :: Map ix (rule,[(ix,formula)])
  }
  deriving (Show)

emptyProof :: Proof ix rule formula
emptyProof = Proof Map.empty Seq.empty Map.empty

add :: (Show ix, Ord ix)
    => Proof ix rule formula -> ix -> formula
    -> Either (Error MLError) (Proof ix rule formula)
add proof ix formula = do
  koreFailWhen
    (Map.member ix (index proof))
    ("A formula with ID '" ++ show ix ++ "already exists")
  return proof
    { index = Map.insert ix (Seq.length (claims proof), formula) (index proof)
    , claims = claims proof |> (ix,formula)
    , derivations = derivations proof
    }

renderProof :: (Ord ix, Show ix, Show rule, Show formula)
            => Proof ix rule formula -> String
renderProof proof = unlines
  [show ix++" : "++show formula++
   case Map.lookup ix (derivations proof) of
     Nothing -> ""
     Just (rule,[]) -> " by "++show rule
     Just (rule,arguments) -> " by "++show rule++" from "++
       unwords (map (show . fst) arguments)
  | (ix,formula) <- toList (claims proof)]

class Eq formula => ProofSystem rule formula | rule -> formula where
  checkDerivation
    :: rule
    -> formula
    -> [formula]
    -> Either (Error MLError) MLSuccess

derive :: (Show ix, Ord ix, ProofSystem rule formula)
       => Proof ix rule formula
       -> ix -> formula -> rule -> [(ix,formula)]
       -> Either (Error MLError) (Proof ix rule formula)
derive proof ix f rule arguments = do
  let
    checkOffset (name,formula) =
      case Map.lookup name (index proof) of
        Nothing -> koreFail ("Formula with ID '" ++ show name ++ " not found.")
        Just (offset,formula') -> do
          koreFailWhen (formula /= formula')
            ("Expected a different formula for id '" ++ show name ++ "'.")
          return offset
    verifyArgument conclusionId conclusionOffset argument = do
      argumentOffset <- checkOffset argument
      koreFailWhen (conclusionOffset <= argumentOffset)
        (  "Hypothesis ('"
        ++ show (fst argument)
        ++ "') must be defined before the conclusion ('"
        ++ show conclusionId
        ++ "')"
        )
      mlSuccess
  offset <- checkOffset (ix,f)
  koreFailWhen (Map.member ix (derivations proof))
    ("Formula with ID '" ++ show ix ++ " already has a derivation.")
  mapM_ (verifyArgument ix offset) arguments
  checkDerivation rule f (map snd arguments)
  return
    (proof { derivations = Map.insert ix (rule,arguments) (derivations proof) })
