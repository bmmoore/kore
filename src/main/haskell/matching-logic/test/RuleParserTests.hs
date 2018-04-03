{-# LANGUAGE FlexibleInstances #-}
module RuleParserTests(ruleParsingTests) where

import           Control.Applicative                           (some)
import           Data.Text                                     (Text)
import qualified Data.Text                                     as T
import           Data.Void
import           Kore.MatchingLogic.HilbertProof
import           Test.Tasty                                    (TestTree,
                                                                testGroup)
import           Test.Tasty.HUnit
import           Text.Megaparsec                               hiding (some)
import           Text.Megaparsec.Char

import           Kore.MatchingLogic.AST
import           Kore.MatchingLogic.ProofSystem.Minimal
import           Kore.MatchingLogic.ProofSystem.Minimal.Syntax


{- Rule Parsing Unit Tests 
    - Each MLRule construct has corresponding test
    - Trivial parsers are used as parameters for the rule parser 
-}

ruleParsingTests =
      testGroup
        "Rule Parser Unit Tests"
        [  prop1Test
          ,prop2Test
          ,prop3Test
          ,mpTest
          ,ugTest
          ,varSubstTest
          ,forAllTest
          ,necessitationTest
          ,propagateOrTest
          ,propagateExistsTest
          ,existsTest
          ,singvarTest
        ]

-- Here, we set up type synonyms, shared by all unit tests 

type DummyParser = Parsec Void Text

type DummySort  = Text
type DummyLabel = Text
type DummyIx    = Int
type DummyVar   = Text
type DummyTerm  = Text

sortParser       :: DummyParser DummySort
labelParser      :: DummyParser DummyLabel
ixParser         :: DummyParser DummyIx
varParser        :: DummyParser DummyVar
termParser       :: DummyParser DummyTerm
mlRuleTestParser :: DummyParser (MLRule DummySort DummyLabel DummyVar DummyTerm DummyIx)

-- Implementations for Dummy Parsers, shared by tests
sortParser       = T.pack <$> some alphaNumChar
labelParser      = T.pack <$> some alphaNumChar
ixParser         = read   <$> some digitChar
varParser        = T.pack <$> some alphaNumChar
termParser       = T.pack <$> some alphaNumChar
mlRuleTestParser = parseMLRule sortParser labelParser varParser mlPatternParser ixParser

mlTestPatterns :: [DummyParser DummyTerm] 

testPatterns = [  "P"
                , "Q"
                , "R" ]

        

mlTestPatterns = string <$> T.pack <$> testPatterns 

mlPatternParser = choice mlTestPatterns


-- Dummy Rule Type instantiated with Dummy Parsers 
type DummyRule = MLRule DummySort DummyLabel DummyVar DummyTerm DummyIx

instance Eq DummyRule where
  (==) a b = let t = (a, b) in case t of 
                (Propositional1 a1 a2, Propositional1 b1 b2)                   -> a1 == b1   && a2 == b2
                (Propositional1 _ _, _)                                        -> False
                (Propositional2 a1 a2 a3, Propositional2 b1 b2 b3)             -> a1 == b1   && a2 == b2 && a3 == b3
                (Propositional2 _ _ _, _)                                      -> False
                (Propositional3 a1 a2, Propositional3 b1 b2)                   -> a1 == b1   && a2 == b2
                (Propositional3 _ _, _)                                        -> False
                (ModusPonens ia1 ia2, ModusPonens ib1 ib2)                     -> ia1 == ib1 && ia2 == ib2
                (ModusPonens _ _, _)                                           -> False
                (Generalization va1 ia1, Generalization va2 ia2)               -> va1 == va2 && ia1 == ia2
                (Generalization _ _, _)                                        -> False
                (VariableSubstitution a1 a2 a3, VariableSubstitution b1 b2 b3) -> a1 == b1   && a2 == b2 && a3 == b3
                (VariableSubstitution _ _ _, _)                                -> False
                (Forall a1 a2 a3, Forall b1 b2 b3)                             -> a1 == b1   && a2 == b2 && a3 == b3
                (Forall _ _ _, _)                                              -> False
                (Necessitation a1 a2 a3, Necessitation b1 b2 b3)               -> a1 == b1   && a2 == b2 && a3 == b3
                (Necessitation _ _ _, _)                                       -> False
                (PropagateOr a1 a2 a3 a4, PropagateOr b1 b2 b3 b4)             -> a1 == b1   && a2 == b2 && a3 == b3 && a4 == b4
                (PropagateOr _ _ _ _, _)                                       -> False
                (PropagateExists a1 a2 a3 a4, PropagateExists b1 b2 b3 b4)     -> a1 == b1   && a2 == b2 && a3 == b3 && a4 == b4
                (PropagateExists _ _ _ _, _)                                   -> False
                (Existence a1, Existence b1)                                   -> a1 == b1
                (Existence _, _)                                               -> False
                (Singvar a1 a2 a3 a4, Singvar b1 b2 b3 b4)                     -> a1 == b1   && a2 == b2 && a3 == b3 && a4 == b4
                (Singvar _ _ _ _, _)                                           -> False

parseTestRule :: String -> DummyRule

parseTestRule ruleStr = case (parse mlRuleTestParser "" (T.pack ruleStr)) of
                          Right parsedRule -> parsedRule

-- Propositional1 Rule Unit Test
prop1RuleStr = "propositional1(P, Q)"

prop1RuleAST =  Propositional1 (T.pack "P") (T.pack "Q")

prop1Test = testCase 
              ("Propositional1") 
                (assertEqual " Propositional1" prop1RuleAST (parseTestRule prop1RuleStr))


-- Propositional2 Rule Unit Test
prop2RuleStr = "propositional2(P, Q, R)"

prop2RuleAST =  Propositional2 (T.pack "P") (T.pack "Q") (T.pack "R")

prop2Test = testCase 
              ("Propositional2") 
                (assertEqual " Propositional2" prop2RuleAST (parseTestRule prop2RuleStr))


-- Propositional3 Rule Unit Test
prop3RuleStr = "propositional3(P,Q)"

prop3RuleAST =  Propositional3 (T.pack "P") (T.pack "Q")

prop3Test = testCase 
              ("Propositional3") 
                (assertEqual " Propositional3 Failure" prop3RuleAST (parseTestRule prop3RuleStr))

-- Modus Ponens Rule Unit Test
mpRuleStr = "mp(1,2)"

mpRuleAST = ModusPonens 1 2

mpTest = testCase 
          ("ModusPonens") 
            (assertEqual " Modus Ponens" mpRuleAST (parseTestRule mpRuleStr))

-- Universal Generalization Rule Test 
ugRuleStr = "ug(x,1)"

ugRuleAST = Generalization (T.pack "x") 1 

ugTest = testCase 
          ("Universal Generalization") 
            (assertEqual " Universal Generalization" ugRuleAST (parseTestRule ugRuleStr))

-- Variable Substitution Test 
varSubstStr = "varsubst(x,1,y)"

varSubstAST = VariableSubstitution (T.pack "x") 1 (T.pack "y") 

varSubstTest = testCase 
          ("Variable Substitution") 
            (assertEqual " Variable Substitution" varSubstAST (parseTestRule varSubstStr))


-- ForAll Test 
forAllStr = "forall(x,P,Q)"

forAllAST = Forall (T.pack "x") (T.pack "P") (T.pack "Q") 

forAllTest = testCase 
          ("ForAll") 
            (assertEqual " ForAll" forAllAST (parseTestRule forAllStr))

-- Necessitation Test
necessitationStr = "necessitation(x, 2, 1)"

necessitationAST = Necessitation (T.pack "x") 2 1

necessitationTest = testCase 
          ("Necessitation") 
            (assertEqual " Necessitation" necessitationAST (parseTestRule necessitationStr))


-- Propagate-Or Test
propagateOrStr = "propagate-or(sigma, 2, P, Q)"

propagateOrAST = PropagateOr (T.pack "sigma") 2 (T.pack "P") (T.pack "Q") 

propagateOrTest = testCase 
          ("PropagateOr") 
            (assertEqual " PropagateOr" propagateOrAST (parseTestRule propagateOrStr))

-- Propagate-Exists Test
propagateExistsStr = "propagate-exists(sigma, 2, x, P)"

propagateExistsAST = PropagateExists (T.pack "sigma") 2 (T.pack "x") (T.pack "P") 

propagateExistsTest = testCase 
          ("PropagateOr") 
            (assertEqual " PropagateExists" propagateExistsAST (parseTestRule propagateExistsStr))

-- Exists Test
existsStr = "exists(x)"

existsAST = Existence (T.pack "x") 

existsTest = testCase 
          ("Existence") 
            (assertEqual " Existence" existsAST (parseTestRule existsStr))

-- SingVar Test
singvarStr = "singvar(x, P, 1, 1)"

singvarAST = Singvar (T.pack "x") (T.pack "P") [1] [1]

singvarTest = testCase 
          ("SingVar") 
            (assertEqual " Singvar" singvarAST (parseTestRule singvarStr))



