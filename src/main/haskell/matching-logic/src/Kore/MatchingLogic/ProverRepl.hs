{-# LANGUAGE MultiParamTypeClasses #-}
module Kore.MatchingLogic.ProverRepl where

import           Kore.MatchingLogic.Error
import           Kore.MatchingLogic.HilbertProof

import           Data.Kore.Error

import           Control.Monad.IO.Class          (liftIO)
import           Control.Monad.State.Strict      (MonadState (..), StateT,
                                                  execStateT, modify')
import           Control.Monad.Trans             (MonadTrans (lift))
import           Data.List                       (isPrefixOf, isSuffixOf)
import qualified Data.Map.Strict                 as Map
import           Data.Text                       (Text, pack)
import           System.Console.Haskeline
import           Text.Parsec
import           Text.Parsec.String

newtype ProverState ix rule formula =
  ProverState (Proof ix rule formula)

data Command id rule formula =
   Add id formula
 | Derive id formula rule [id]
 deriving Show

applyCommand :: (Show id, Ord id, ProofSystem rule formula)
             => Command id rule formula
             -> Proof id rule formula
             -> Either (Error MLError) (Proof id rule formula)
applyCommand command proof = case command of
  Add id f -> add proof id f
  Derive id f rule argIds -> do
    let
      findTerm ix =
        case Map.lookup ix (index proof) of
          Just (_, term) -> return term
          Nothing -> koreFail ("Formula with id '" ++ show ix ++ "' not found.")
    argTerms <- mapM findTerm argIds
    derive proof id f rule (zip argIds argTerms)

parseCommand
  :: Parser id
  -> Parser formula
  -> Parser (rule,[id])
  -> Parser (Command id rule formula)
parseCommand pId pFormula pDerivation = do
  id <- pId
  spaces
  char ':'
  spaces
  formula <- pFormula
  spaces
  option (Add id formula)
    (do string "by"
        spaces
        (rule,argIds) <- pDerivation
        return (Derive id formula rule argIds))

runProver :: (Ord ix, ProofSystem rule formula, Show ix, Show rule, Show formula)
          => Parser (Command ix rule formula)
          -> ProverState ix rule formula
          -> IO (ProverState ix rule formula)
runProver pCommand initialState =
  execStateT (runInputT defaultSettings startRepl) initialState
 where
   startRepl = outputStrLn "Matching Logic prover started" >> repl
   repl = do
     mcommand <- getInputLine ">>> "
     case mcommand of
       Just command -> case parse pCommand "<stdin>" command of
         Left err -> outputStrLn (show err) >> repl
         Right cmd -> do
           outputStrLn (show cmd)
           ProverState state <- lift get
           case applyCommand cmd state of
             Right state' -> do
               lift (put (ProverState state'))
               outputStrLn (renderProof state')
               repl
             Left err ->
              outputStrLn ("command failed" ++ printError err) >> repl
       Nothing -> return ()
