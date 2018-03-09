{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Kore.MatchingLogic.Proofs.ProofAssistantTest (proofAssistantTests) where

import           Test.Tasty                       (TestTree, testGroup)
import           Test.Tasty.HUnit                 (assertFailure, testCase)

import           Data.Kore.AST.Kore
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts
import           Data.Kore.Error

import           Kore.MatchingLogic.Error
import           Kore.MatchingLogic.HilbertProof  as HilbertProof (Proof (..),
                                                                   add, derive,
                                                                   emptyProof)
import           Kore.MatchingLogic.MLProofSystem (MLRule (..))

import           Control.Monad                    (foldM)
import           Data.List                        (foldl')
import qualified Data.Map.Strict                  as Map

proofAssistantTests :: TestTree
proofAssistantTests =
    testGroup "MLProof Assistant"
        [ runTestScript
            "Simple MLProof for phi implies phi."
            [ testAddGoal
                phi
                (NewGoalId 6)
            , testAddGoal
                (metaImplies phiSort phi phi)
                (NewGoalId 7)
            , testAddGoal
                (metaImplies phiSort phi (metaImplies phiSort phi phi))
                (NewGoalId 2)
            , testAddGoal
                (metaImplies phiSort
                    phi
                    (metaImplies phiSort (metaImplies phiSort phi phi) phi)
                )
                (NewGoalId 4)
            , testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort phi
                        (metaImplies phiSort (metaImplies phiSort phi phi) phi)
                    )
                    (metaImplies phiSort
                        (metaImplies phiSort phi (metaImplies phiSort phi phi))
                        (metaImplies phiSort phi phi)
                    )
                )
                (NewGoalId 5)
            , testAddGoal
                (metaImplies phiSort
                    (metaImplies phiSort phi (metaImplies phiSort phi phi))
                    (metaImplies phiSort phi phi)
                )
                (NewGoalId 3)
            , testAddGoal (metaImplies phiSort phi phi) (NewGoalId 1)

            , assertGoalCount 7
            , assertGoal (GoalId 1) (metaImplies phiSort phi phi)
            , assertGoal
                (GoalId 2)
                (metaImplies phiSort phi (metaImplies phiSort phi phi))
            , assertGoal (GoalId 3)
                (metaImplies phiSort
                    (metaImplies phiSort phi (metaImplies phiSort phi phi))
                    (metaImplies phiSort phi phi)
                )
            , assertGoal (GoalId 4)
                (metaImplies phiSort
                    phi
                    (metaImplies phiSort (metaImplies phiSort phi phi) phi)
                )
            , assertGoal (GoalId 5)
                (metaImplies phiSort
                    (metaImplies phiSort
                        phi
                        (metaImplies phiSort (metaImplies phiSort phi phi) phi)
                    )
                    (metaImplies phiSort
                        (metaImplies phiSort phi (metaImplies phiSort phi phi))
                        (metaImplies phiSort phi phi)
                    )
                )
            , assertGoal (GoalId 6) phi
            , assertGoal (GoalId 7) (metaImplies phiSort phi phi)

            , assertUnproven (GoalId 1)
            , assertUnproven (GoalId 2)
            , assertUnproven (GoalId 3)
            , assertUnproven (GoalId 4)
            , assertUnproven (GoalId 5)
            , assertUnproven (GoalId 6)
            , assertUnproven (GoalId 7)

            , testModusPonens
                (GoalId 2)
                (GoalId 3)
                (GoalId 1)
            , assertGoalCount 7
            , assertPartlyProven (GoalId 1) (GoalNeeds [GoalId 3, GoalId 2])
            , assertUnproven (GoalId 2)
            , assertUnproven (GoalId 3)
            , assertUnproven (GoalId 4)
            , assertUnproven (GoalId 5)
            , assertUnproven (GoalId 6)
            , assertUnproven (GoalId 7)

            , testModusPonens
                (GoalId 4)
                (GoalId 5)
                (GoalId 3)
            , assertGoalCount 7
            , assertPartlyProven (GoalId 1) (GoalNeeds [GoalId 3, GoalId 2])
            , assertUnproven (GoalId 2)
            , assertPartlyProven (GoalId 3) (GoalNeeds [GoalId 5, GoalId 4])
            , assertUnproven (GoalId 4)
            , assertUnproven (GoalId 5)
            , assertUnproven (GoalId 6)
            , assertUnproven (GoalId 7)

            , testProposition2 (GoalId 6) (GoalId 7) (GoalId 6) (GoalId 5)
            , assertGoalCount 7
            , assertPartlyProven (GoalId 1) (GoalNeeds [GoalId 3, GoalId 2])
            , assertUnproven (GoalId 2)
            , assertPartlyProven (GoalId 3) (GoalNeeds [GoalId 4])
            , assertUnproven (GoalId 4)
            , assertProven (GoalId 5)
            , assertUnproven (GoalId 6)
            , assertUnproven (GoalId 7)

            , testProposition1 (GoalId 6) (GoalId 7) (GoalId 4)
            , assertGoalCount 7
            , assertPartlyProven (GoalId 1) (GoalNeeds [GoalId 2])
            , assertUnproven (GoalId 2)
            , assertProven (GoalId 3)
            , assertProven (GoalId 4)
            , assertProven (GoalId 5)
            , assertUnproven (GoalId 6)
            , assertUnproven (GoalId 7)

            , testProposition1 (GoalId 6) (GoalId 6) (GoalId 2)
            , assertGoalCount 7
            , assertProven (GoalId 1)
            , assertProven (GoalId 2)
            , assertProven (GoalId 3)
            , assertProven (GoalId 4)
            , assertProven (GoalId 5)
            , assertUnproven (GoalId 6)
            , assertUnproven (GoalId 7)
            ]
        ]
  where
    phi = metaVariable "#phi" phiSort
    phiSort = MetaSortVariable1 "#s"

-- TODO: Tests with failures to do things, e.g. using undefined IDs.

newtype NewGoalId = NewGoalId Int
newtype GoalId = GoalId Int
    deriving (Eq, Show, Ord)
type MLProof = Proof GoalId (MLRule GoalId) UnifiedPattern
data GoalMLProofState
    = GoalUnproven
    | GoalProven
    | GoalPartlyProven GoalNeeds
    deriving Show
newtype GoalNeeds = GoalNeeds [GoalId]
    deriving (Eq, Show)
emptyMLProof :: MLProof
emptyMLProof = emptyProof
goalCount :: MLProof -> Int
goalCount proof = length (claims proof)

stringError :: Either (Error MLError) a -> Either String a
stringError thing =
    case thing of
        Right x  -> Right x
        Left err -> Left (printError err)


addGoal
    :: UnifiedPattern -> NewGoalId -> MLProof -> Either String MLProof
addGoal formula (NewGoalId goalId) proof =
    stringError (HilbertProof.add proof (GoalId goalId) formula)
modusPonens
    :: GoalId -> GoalId -> GoalId -> MLProof -> Either String MLProof
modusPonens hypothesisFirstId hypothesisSecondId conclusionId proof =
    stringError
        (modusPonens' hypothesisFirstId hypothesisSecondId conclusionId proof)
  where
    modusPonens' hypothesisFirstId hypothesisSecondId conclusionId proof = do
        hypothesisFirstFormula <- lookupFormula hypothesisFirstId proof
        hypothesisSecondFormula <- lookupFormula hypothesisSecondId proof
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (ModusPonens hypothesisFirstId hypothesisSecondId)
            [ (hypothesisFirstId, hypothesisFirstFormula)
            , (hypothesisSecondId, hypothesisSecondFormula)
            ]

proposition1 :: GoalId -> GoalId -> GoalId -> MLProof -> Either String MLProof
proposition1 phiId psiId conclusionId proof =
    stringError (proposition1' phiId psiId conclusionId proof)
  where
    proposition1' phiId psiId conclusionId proof = do
        phi <- lookupFormula phiId proof
        psi <- lookupFormula psiId proof
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Propositional1 phiId psiId)
            [ (phiId, phi), (psiId, psi) ]

proposition2
    :: GoalId -> GoalId -> GoalId -> GoalId -> MLProof -> Either String MLProof
proposition2 phi1Id phi2Id phi3Id conclusionId proof =
    stringError (proposition2' phi1Id phi2Id phi3Id conclusionId proof)
  where
    proposition2' phi1Id phi2Id phi3Id conclusionId proof = do
        phi1 <- lookupFormula phi1Id proof
        phi2 <- lookupFormula phi2Id proof
        phi3 <- lookupFormula phi3Id proof
        conclusionFormula <- lookupFormula conclusionId proof
        derive
            proof
            conclusionId
            conclusionFormula
            (Propositional2 phi1Id phi2Id phi3Id)
            [ (phi1Id, phi1), (phi2Id, phi2), (phi3Id, phi3) ]

-- Inefficient implementation, but good enough for tests.
goalState :: GoalId -> MLProof -> Maybe GoalMLProofState
goalState goalId proof =
    case Map.lookup goalId (index proof) of
        Nothing -> Nothing
        _ ->
            case Map.lookup goalId (derivations proof) of
                Nothing -> Just GoalUnproven
                Just (ModusPonens{}, indexAndFormula) ->
                    snd
                        (foldl'
                            combineStates
                            (goalId, Just GoalProven)
                            (map
                                (goalStateAndIndex proof . fst)
                                indexAndFormula
                            )
                        )
                Just (Propositional1{}, _) -> Just GoalProven
                Just (Propositional2{}, _) -> Just GoalProven
                Just (Propositional3{}, _) -> Just GoalProven
  where
    goalStateAndIndex proof idx = (idx, goalState idx proof)
    combineStates (idx, Nothing) _ =
        (idx, Nothing)
    combineStates (idx, _) (_, Nothing) =
        (idx, Nothing)
    combineStates state (childIdx, Just GoalProven) = state
    combineStates (idx, Just GoalProven) (childIdx, _) =
        (idx, Just (GoalPartlyProven (GoalNeeds [childIdx])))
    combineStates
        (idx, Just (GoalPartlyProven (GoalNeeds idxs)))
        (childIdx, _)
      =
        (idx, Just (GoalPartlyProven (GoalNeeds (childIdx:idxs))))

lookupGoal :: GoalId -> MLProof -> Maybe UnifiedPattern
lookupGoal goalId proof = snd <$> Map.lookup goalId (index proof)

lookupFormula :: GoalId -> MLProof -> Either (Error MLError) UnifiedPattern
lookupFormula goalId proof =
    case Map.lookup goalId (index proof) of
        Nothing ->
            koreFail ("Formula with ID '" ++ show goalId ++ "' not found.")
        Just (_, formula) -> return formula

testAddGoal
    :: AsAst UnifiedPattern p
    => p
    -> NewGoalId
    -> (String, MLProof -> Either String MLProof)
testAddGoal pattern1 (NewGoalId goalId) =
    ( "adding " ++ show unifiedPattern ++ " with ID=" ++ show goalId
    , addGoal unifiedPattern (NewGoalId goalId)
    )
  where
    unifiedPattern = asAst pattern1

testModusPonens
    :: GoalId
    -> GoalId
    -> GoalId
    -> (String, MLProof -> Either String MLProof)
testModusPonens implierId implicationId impliedId =
    ( "modus ponens with phi=" ++ show implierId
        ++ " phi->psi=" ++ show implicationId
        ++ " and psi=" ++ show impliedId
    , modusPonens implierId implicationId impliedId
    )

testProposition2
    :: GoalId -> GoalId -> GoalId -> GoalId
    -> (String, MLProof -> Either String MLProof)
testProposition2 phi1 phi2 phi3 conclusion =
    ( "proposition 2 with phi1=" ++ show phi1
        ++ " phi2=" ++ show phi2
        ++ " phi3=" ++ show phi3
        ++ " conclusion=" ++ show conclusion
    , proposition2 phi1 phi2 phi3 conclusion
    )

testProposition1
    :: GoalId -> GoalId -> GoalId
    -> (String, MLProof -> Either String MLProof)
testProposition1 phi psi conclusion =
    ( "proposition 1 with phi="
        ++ show phi
        ++ " psi="
        ++ show psi
        ++ " conclusion="
        ++ show conclusion
    , proposition1 phi psi conclusion
    )

assertGoalCount :: Int -> (String, MLProof -> Either String MLProof)
assertGoalCount count =
    ( "expecting the goal count to be " ++ show count
    , goalCountAssertion count
    )
goalCountAssertion :: Int -> (MLProof -> Either String MLProof)
goalCountAssertion count proof =
    if count == actualGoalCount
        then Right proof
        else Left ("actual goal count is " ++ show actualGoalCount)
  where
    actualGoalCount = goalCount proof

assertGoal
    :: AsAst UnifiedPattern p
    => GoalId
    -> p
    -> (String, MLProof -> Either String MLProof)
assertGoal goalId pattern1 =
    ( "expecting the goal to be " ++ show unifiedPattern
    , goalAssertion goalId unifiedPattern
    )
  where
    unifiedPattern = asAst pattern1
goalAssertion
    :: GoalId
    -> UnifiedPattern
    -> (MLProof -> Either String MLProof)
goalAssertion goalId pattern1 proof =
    case lookupGoal goalId proof of
        Nothing -> Left ("Goal with id " ++ show goalId ++ " not found.")
        Just actualPattern ->
            if actualPattern /= pattern1
                then Left ("the actual goal is" ++ show actualPattern)
                else Right proof

assertUnproven :: GoalId -> (String, MLProof -> Either String MLProof)
assertUnproven (GoalId goalId) =
    ( "expecting the goal with id #" ++ show goalId ++ " to be unproven"
    , unprovenAssertion (GoalId goalId)
    )
unprovenAssertion :: GoalId -> (MLProof -> Either String MLProof)
unprovenAssertion goalId proof =
    case goalState goalId proof of
        Just GoalUnproven -> Right proof
        state             -> Left ("the goal is " ++ show state)

assertPartlyProven
    :: GoalId
    -> GoalNeeds
    -> (String, MLProof -> Either String MLProof)
assertPartlyProven (GoalId goalId) expectedDependencies =
    ( "expecting the goal with id #" ++ show goalId ++ " to be partly proven"
    , partlyProvenAssertion (GoalId goalId) expectedDependencies
    )
partlyProvenAssertion
    :: GoalId
    -> GoalNeeds
    -> (MLProof -> Either String MLProof)
partlyProvenAssertion goalId expectedDependencies proof =
    case goalState goalId proof of
        Just (GoalPartlyProven actualDependencies) ->
            if actualDependencies /= expectedDependencies
                then
                    Left
                        (  "different unproven dependencies, expected="
                        ++ show expectedDependencies
                        ++ " actual="
                        ++ show actualDependencies)
                else Right proof
        state -> Left ("the goal is " ++ show state)

assertProven :: GoalId -> (String, MLProof -> Either String MLProof)
assertProven (GoalId goalId) =
    ( "expecting the goal with id #" ++ show goalId ++ " to be proven"
    , provenAssertion (GoalId goalId)
    )
provenAssertion :: GoalId -> (MLProof -> Either String MLProof)
provenAssertion goalId proof =
    case goalState goalId proof of
        Just GoalProven -> Right proof
        state           -> Left ("the goal is " ++ show state)

runTestScript
    :: String
    -> [(String, MLProof -> Either String MLProof)]
    -> TestTree
runTestScript description actions =
    testCase description
        (case foldM runAction emptyMLProof actionsWithDescriptions of
            Left err -> assertFailure err
            Right _  -> return ()
        )
  where
    actionName index (description1, action) =
        ("Action #" ++ show index ++ " (" ++ description1 ++ ")", action)
    actionsWithDescriptions = zipWith actionName [(0::Int)..] actions

runAction
    :: MLProof
    -> (String, MLProof -> Either String MLProof)
    -> Either String MLProof
runAction proof (description, action) =
    case action proof of
        Left err -> Left (description ++ " : " ++ err)
        result   -> result
