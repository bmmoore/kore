{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DisambiguateRecordFields   #-}
{-# LANGUAGE DuplicateRecordFields      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE PartialTypeSignatures   #-}
module Kore.MatchingLogic.ProofSystem.OnePlusOne where
import           Control.Lens
import           Data.Data
import qualified Data.Map.Strict                        as Map
import qualified Data.Set                               as Set
import qualified Data.Tree                              as Tree

import           GHC.Generics
import           Prelude                                hiding (all, and, not,
                                                         succ)

import           Kore.MatchingLogic.AST                 (applicationP)
import qualified Kore.MatchingLogic.AST                 as AST
import           Kore.MatchingLogic.HilbertProof        as HilbertProof (Proof (..),
                                                                         ProofSystem,
                                                                         add,
                                                                         derive,
                                                                         emptyProof)
import           Kore.MatchingLogic.ProofSystem.Minimal ( MLRule (..)
                                                        , MLRuleSig
                                                        , transformRule
                                                        , SubstitutedVariable (..)
                                                        , SubstitutingVariable (..))
import           Kore.MatchingLogic.Signature.Simple

import           Control.Monad                          (foldM)
import           Control.Monad.State.Strict
import           Data.Functor.Foldable                  (Fix (Fix))
import           Data.List                              (foldl')
import qualified Data.Map.Strict                        as Map
import           Data.Store
import           Data.Text                              (Text)
import           Data.Text.Prettyprint.Doc

import qualified Data.ByteString                        as B
import           Data.IntMap                            (IntMap)
import qualified Data.IntMap                            as IntMap

-- START code extracted from Coq
data Nat =
   O
 | S Nat
  deriving (Read,Show,Eq,Generic,Data)

data Formula =
   Plus Formula Formula
 | Succ Formula
 | Zero
 | Not Formula
 | And Formula Formula
 | Var Nat
 | All Nat Formula
 | Defined Formula
  deriving (Read,Show,Eq,Generic,Data)

data Ctx =
   SuccC
 | PlusLC Formula
 | PlusRC Formula
 | DefinedC
  deriving (Read,Show,Eq,Generic,Data)

data Ctx_path =
   Path_nil
 | Path_cons Ctx Ctx_path
  deriving (Read,Show,Eq,Generic,Data)

data Simple_rule =
   Rule_mp Simple_proof Simple_proof
 | Rule_frame Ctx Simple_proof
 | Rule_gen Nat Simple_proof
 | Rule_use_hyp Nat
 | Ax_propositional1 Formula Formula
 | Ax_propositional2 Formula Formula Formula
 | Ax_propositional3 Formula Formula
 | Ax_varSubst Nat Nat Formula Formula
 | Ax_allImp Nat Formula Formula
 | Ax_out_ex Ctx Nat Formula
 | Ax_out_or Ctx Formula Formula
 | Ax_existence Nat
 | Ax_singvar Ctx_path Ctx_path Nat Formula
 | Ax_definedness
 | Ax_proj1 Formula Formula
 | Ax_proj2 Formula Formula
 | Ax_and_intro Formula Formula
 | Ax_or_elim Formula Formula Formula
 | Ax_or_intro1 Formula Formula
 | Ax_or_intro2 Formula Formula
 | Ax_zero_functional
 | Ax_succ_functional
  deriving (Read,Show,Eq,Generic,Data)

data Simple_proof =
   Conclusion Formula Simple_rule
  deriving (Read,Show,Eq,Generic,Data)
-- END code extracted from Coq.

instance Store Nat
instance Store Formula
instance Store Ctx
instance Store Ctx_path
instance Store Simple_rule
instance Store Simple_proof

instance Plated Simple_proof

nat2Int n = go 0 n
  where go !x O      = x
        go !x (S n') = go (x+1) n'

ctxRule :: (Text -> Int -> a) -> Ctx -> a
ctxRule f SuccC      = f "succ" 0
ctxRule f (PlusLC _) = f "plus" 0
ctxRule f (PlusRC _) = f "plus" 1
ctxRule f DefinedC   = f "defined" 0

convertCtxRule :: Ctx -> ix -> MLRule sort Text var term ix
convertCtxRule SuccC      = Framing "succ" 0
convertCtxRule (PlusLC _) = Framing "plus" 0
convertCtxRule (PlusRC _) = Framing "plus" 1
convertCtxRule DefinedC   = Framing "defined" 0

convertPath :: Ctx_path -> [Int]
convertPath Path_nil           = []
convertPath (Path_cons ctx cs) = ctxRule (const (:)) ctx (convertPath cs)

convertRule :: (Monad m)
            => (Simple_proof -> m Int)
            -> Simple_rule -> m (Either Int
                                 (MLRule Text Text Int (AST.Pattern Text Text Int) Int))
convertRule convertHyp r = case r of
  Rule_mp h1 h2 -> Right <$> (ModusPonens <$> convertHyp h2 <*> convertHyp h1)
  -- ^ NB. argument order is flipped!
  Rule_frame ctx hyp -> Right . convertCtxRule ctx <$> convertHyp hyp
  Rule_gen v hyp -> Right . Generalization (nat2Int v) <$> convertHyp hyp
  Rule_use_hyp v -> return (Left (3+nat2Int v))
  Ax_definedness -> return (Left 0)
  Ax_zero_functional -> return (Left 1)
  Ax_succ_functional -> return (Left 2)
  axiom -> pure . Right $ case axiom of
    Ax_propositional1 f1 f2 -> Propositional1 (convertFormula f1) (convertFormula f2)
    Ax_propositional2 f1 f2 f3 -> Propositional2 (convertFormula f1) (convertFormula f2) (convertFormula f3)
    Ax_propositional3 f1 f2 -> Propositional3 (convertFormula f1) (convertFormula f2)
    Ax_varSubst x y p1 p2 -> VariableSubstitution (SubstitutedVariable (nat2Int x))
                                                  (convertFormula p1)
                                                  (SubstitutingVariable (nat2Int y))
    Ax_allImp x f1 f2 -> ForallRule (nat2Int x) (convertFormula f1) (convertFormula f2)
    Ax_out_ex ctx var p -> ctxRule PropagateExists ctx (nat2Int var) (convertFormula p)
    Ax_out_or ctx f1 f2 -> ctxRule PropagateOr ctx (convertFormula f1) (convertFormula f2)
    Ax_existence v -> Existence (nat2Int v)
    Ax_singvar path1 path2 v f -> Singvar (nat2Int v) (convertFormula f) (convertPath path1) (convertPath path2)
    Ax_proj1 f1 f2 -> Proj1 (convertFormula f1) (convertFormula f2)
    Ax_proj2 f1 f2 -> Proj2 (convertFormula f1) (convertFormula f2)
    Ax_and_intro f1 f2 -> AndIntro (convertFormula f1) (convertFormula f2)
    Ax_or_elim f1 f2 f3 -> OrElim (convertFormula f1) (convertFormula f2) (convertFormula f3)
    Ax_or_intro1 f1 f2 -> OrIntroL (convertFormula f1) (convertFormula f2)
    Ax_or_intro2 f1 f2 -> OrIntroR (convertFormula f1) (convertFormula f2)

convertFormula :: Formula -> TextPat
convertFormula f = case f of
    Plus f1 f2 -> app "plus" [convertFormula f1, convertFormula f2]
    Succ f1    -> app "succ" [convertFormula f1]
    Zero       -> app "zero" []
    Not f1     -> not (convertFormula f1)
    And f1 f2  -> and (convertFormula f1) (convertFormula f2)
    Var n      -> var (nat2Int n)
    All n f1   -> all (nat2Int n) (convertFormula f1)
    Defined f1 -> app "defined" [convertFormula f1]
  where
    app label args = Fix (AST.Application label args)
    and f1 f2 = Fix (AST.And "Nat" f1 f2)
    all v body = Fix (AST.Forall "Nat" "Nat" v body)
    var v = Fix (AST.Variable "Nat" v)
    not f = Fix (AST.Not "Nat" f)

-- ProofSystem MLError (MLRuleSig sig var) (WFPattern sig var) where

type TextPat = AST.Pattern Text Text Int
type TextRule = MLRule Text Text Int TextPat
newtype ConvM a = ConvM {runConvM :: State (Int, [(Int,TextPat,TextRule Int)]) a}
  deriving (Functor,Applicative,Monad)

plusSignature :: ValidatedSignature
Just plusSignature = validate $ SignatureInfo
  (Set.fromList ["Nat"])
  (Map.fromList [("defined",("Nat",["Nat"]))
                ,("zero",("Nat",[]))
                ,("succ",("Nat",["Nat"]))
                ,("plus",("Nat",["Nat","Nat"]))
                ])

emit :: TextPat -> TextRule Int -> ConvM Int
emit pat rule = ConvM (state (\(next,lines) -> (next,(next+1,(next,pat,rule):lines))))

-- convert :: Simple_proof -> [_] -> [(Int,...)]
--convert :: Simple_proof ->

convert :: Simple_proof -> ConvM Int
convert (Conclusion formula rule) = convertRule convert rule >>= \case
    Right rule -> emit (convertFormula formula) rule
    Left ix' -> return ix'

useHyp :: (Applicative f) => (Nat -> f Nat) -> (Simple_proof -> f Simple_proof)
useHyp f (Conclusion pat (Rule_use_hyp v)) = Conclusion pat . Rule_use_hyp <$> f v
useHyp f proof = pure proof

loadCoqOutput :: IO Simple_proof
loadCoqOutput = do
  text <- readFile "/home/brandon/code/k6/kore/src/main/haskell/matching-logic/test/resources/proof_tree.txt"
  return $! read text

loadCoqOutput2 :: IO Simple_proof
loadCoqOutput2 = do
  text <- readFile "/home/brandon/code/k6/kore/src/main/haskell/matching-logic/test/resources/proof2.txt"
  return $! read text

saveProofBin :: Simple_proof -> IO ()
saveProofBin proof =
  B.writeFile "/home/brandon/code/k6/kore/src/main/haskell/matching-logic/test/resources/proof_tree.bin" (encode proof)

loadProofBin :: IO Simple_proof
loadProofBin = do
  bytes <- B.readFile "/home/brandon/code/k6/kore/src/main/haskell/matching-logic/test/resources/proof_tree.bin"
  case decode bytes of
    Left err -> error (show err)
    Right v  -> return v

runConversion :: Int -> Simple_proof -> [(Int,TextPat,TextRule Int)]
runConversion numHyps proof =
  let (_,proofLines) = execState (runConvM (convert proof)) (numHyps,[])
  in reverse proofLines

checkRule :: (ReifiesSignature s)
          => TextRule hypId
          -> Maybe (MLRuleSig (SimpleSignature s) Int hypId)
checkRule = transformRule resolveSort resolveLabel pure checkPattern pure

checkPattern :: (ReifiesSignature s)
             => TextPat -> Maybe (AST.WFPattern (SimpleSignature s) Int)
checkPattern = resolvePattern >=> AST.checkSorts

checkEntry :: (ReifiesSignature s)
           => (Int,TextPat,TextRule Int)
           -> Maybe (Int,AST.WFPattern (SimpleSignature s) Int, MLRuleSig (SimpleSignature s) Int Int)
checkEntry (ix,pat,rule) = (,,) ix <$> checkPattern pat <*> checkRule rule

checkEntry' :: (ReifiesSignature s)
            => proxy (SimpleSignature s)
            -> (Int,TextPat,TextRule Int)
            -> Maybe (Int,AST.WFPattern (SimpleSignature s) Int, MLRuleSig (SimpleSignature s) Int Int)
checkEntry' _proxy = checkEntry


balance :: String -> Tree.Tree String
balance str = go 0 "<TOP>" [] [] str
  where
    go depth parent siblings stack string@('(':string')
      = go (depth+1) string [] ((parent,siblings):stack) string'
    go depth parent siblings ((grandparent,siblings'):stack) string@(')':string')
      = go (depth-1) grandparent (Tree.Node parent (reverse siblings):siblings') stack string'
    go 0 _ [n] [] "" = n
    go depth parent siblings stack (_:string) =
      go depth parent siblings stack string

filterTree :: (a -> Bool) -> Tree.Tree a -> Tree.Forest a
filterTree pred t@(Tree.Node x children) =
  let children' = concatMap (filterTree pred) children
  in if pred x then [Tree.Node x children'] else children'

leaves :: Tree.Tree a -> Tree.Forest a
leaves t@(Tree.Node _ children)
    | null children = [t]
    | otherwise = concatMap leaves children

chomp :: String -> String
chomp str = go 0 str
  where
    go depth ('(':str) = '(':go (depth+1) str
    go 1     (')':str) = ")"
    go depth (')':str) = ')':go (depth-1) str
    go depth (c  :str) = c:go depth str

findBadThings :: ReifiesSignature s
              => proxy (SimpleSignature s)
              -> [(Int,TextPat,TextRule Int)]
              -> [(Int,TextPat,TextRule Int)]
findBadThings proxy entries =
  [e | e <- entries, checkEntry' proxy e == Nothing]

loadConverted :: IO [(Int,TextPat,TextRule Int)]
loadConverted = do
  p <- loadProofBin
  return (runConversion 5 p)

startProof :: (ReifiesSignature s)
           => proxy (SimpleSignature s)
           -> Either String (Proof Int
                       (MLRuleSig (SimpleSignature s) Int)
                       (AST.WFPattern (SimpleSignature s) Int))
startProof _proxy = do
  assumptions <- maybe (Left "Bad pattern") Right $ mapM checkPattern
    [defined (var 0)
    -- ^ definedness
    ,ex 1 (eqlP (var 1) zero)
    -- ^ zero functional
    ,ex 1 (eqlP (var 1) (succ (var 0)))
    -- ^ succ functional
    ,AST.impliesP "Nat" (plus zero (var 0)) (var 0)
    -- ^ definition of plus zero
    ,AST.impliesP "Nat" (plus (succ (var 0)) (var 1)) (succ (plus (var 0) (var 1)))
    -- ^ definition of plus succ
    ]
  foldM (\pf (ix,pat) -> either (Left . show) Right $ add (\_->Right ()) pf ix pat)
      emptyProof (zip [0..] assumptions)
  where
    defined p = AST.applicationP "defined" [p]
    zero = AST.applicationP "zero" []
    succ p = AST.applicationP "succ" [p]
    plus a b = AST.applicationP "plus" [a,b]
    total p = AST.notP "Nat" (defined (AST.notP "Nat" p))
    ex n = AST.existsP "Nat" "Nat" n
    var n = AST.variableP "Nat" n
    eqlP l r = total (AST.iffP "Nat" l r)

runEntry :: (ReifiesSignature s)
         => Proof Int
              (MLRuleSig (SimpleSignature s) Int)
              (AST.WFPattern (SimpleSignature s) Int)
         -> (Int,AST.WFPattern (SimpleSignature s) Int,
              MLRuleSig (SimpleSignature s) Int Int)
         -> Either String (Proof Int
              (MLRuleSig (SimpleSignature s) Int)
              (AST.WFPattern (SimpleSignature s) Int))
runEntry proof entry@(ix,pat,rule) = either (\err -> Left $
     "Error processing "++show entry++":\n"++show err) Right $ do
    proof1 <- add (const (Right ())) proof ix pat
    derive proof1 ix pat rule

withProof :: (forall s. (ReifiesSignature s) =>
              Either String (Proof Int
                      (MLRuleSig (SimpleSignature s) Int)
                      (AST.WFPattern (SimpleSignature s) Int))
              -> IO r)
          -> IO r
withProof body = do
  entries <- loadConverted
  reifySignature plusSignature (\proxy -> body $ do
      axioms <- startProof proxy
      foldM (\pf -> (maybe (Left "Check failed") Right . checkEntry) >=> runEntry pf) axioms entries)

example :: IO [(Int,TextPat,TextRule Int)]
example = do
  entries <- loadConverted
  return $ reifySignature plusSignature (flip findBadThings entries)

main ::  IO ()
main = withProof (putStrLn . either id (const "Success"))
