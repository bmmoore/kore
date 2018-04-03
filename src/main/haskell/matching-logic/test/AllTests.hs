{-# LANGUAGE FlexibleInstances #-}

import           Test.Tasty                (TestTree, testGroup)

import           Test.Tasty.HUnit
import           Test.Tasty.Runners        (consoleTestReporter,
                                            defaultMainWithIngredients,
                                            listingTests)
import           Test.Tasty.Runners.AntXML (antXMLRunner)


import           Text.Megaparsec
import           Text.Megaparsec.Char

import           RuleParserTests

main :: IO ()

main = do
    defaultMainWithIngredients
        [antXMLRunner, listingTests, consoleTestReporter]
        allParserTests

allParserTests :: TestTree
allParserTests =
    testGroup
        " All Matching Logic Tests"
        [ unitTests
        ]

unitTests :: TestTree
unitTests =
    testGroup
        " Unit Tests"
        [ parserUnitTests
        ]


parserUnitTests :: TestTree
parserUnitTests = testGroup
                    " All Parser Unit Tests"
                    [ ruleParsingTests
                    ]
