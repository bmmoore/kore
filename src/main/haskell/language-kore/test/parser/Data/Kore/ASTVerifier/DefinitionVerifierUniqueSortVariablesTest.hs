module Data.Kore.ASTVerifier.DefinitionVerifierUniqueSortVariablesTest
    (definitionVerifierUniqueSortVariablesTests) where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error
import           Data.Kore.ImplicitDefinitions

definitionVerifierUniqueSortVariablesTests :: TestTree
definitionVerifierUniqueSortVariablesTests =
    testGroup
        "Definition verifier - unique sort variables - unit tests"
        [ expectSuccess "Simplest definition"
            (simpleDefinitionFromSentences (ModuleName "MODULE") [])
        , expectSuccess "Definition with sort"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ sortSentenceWithSortParameters (SortName "s") [] ]
            )
        , expectSuccess "Sort with one sort parameter"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ sortSentenceWithSortParameters
                    (SortName "s")
                    [ sortVariable Object (SortVariableName "sv1") ]
                ]
            )
        , expectSuccess "Sort with one sort parameter with same name"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ sortSentenceWithSortParameters
                    (SortName "s")
                    [ sortVariable Object (SortVariableName "s") ]
                ]
            )
        , expectSuccess "Sort with two sort parameters"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ sortSentenceWithSortParameters
                    (SortName "s")
                    [ sortVariable Object (SortVariableName "sv1")
                    , sortVariable Object (SortVariableName "sv2")
                    ]
                ]
            )
        ------------------------------------------------------------------
        , expectSuccess "Definition with meta alias"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaAliasSentenceWithSortParameters
                    (AliasName "#a") charListMetaSort []
                ]
            )
        , expectSuccess "Meta alias with one sort parameter"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaAliasSentenceWithSortParameters
                    (AliasName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#sv") ]
                ]
            )
        , expectSuccess "Meta alias with one sort parameter with same name"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaAliasSentenceWithSortParameters
                    (AliasName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#a") ]
                ]
            )
        , expectSuccess
            "Meta alias with one sort parameter with same name as sort"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaAliasSentenceWithSortParameters
                    (AliasName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#String") ]
                ]
            )
        , expectSuccess
            "Meta alias with two sort parameters"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaAliasSentenceWithSortParameters
                    (AliasName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#sv1")
                    , sortVariable Meta (SortVariableName "#sv2")
                    ]
                ]
            )
        ------------------------------------------------------------------
        , expectSuccess "Definition with object alias"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceAliasSentence
                    (aliasSentenceWithSortParameters
                        (AliasName "a") (SortName "s") [])
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Object alias with one sort parameter"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceAliasSentence
                    (aliasSentenceWithSortParameters
                        (AliasName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName "sv") ])
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Object alias with one sort parameter with same name"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceAliasSentence
                    (aliasSentenceWithSortParameters
                        (AliasName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName "a") ])
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess
            "Object alias with one sort parameter with same name as sort"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceAliasSentence
                    (aliasSentenceWithSortParameters
                        (AliasName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName "s") ])
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Object alias with two sort parameters"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceAliasSentence
                    (aliasSentenceWithSortParameters
                        (AliasName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName "sv1")
                        , sortVariable Object (SortVariableName "sv2")
                        ])
                , simpleSortSentence (SortName "s")
                ]
            )
        ------------------------------------------------------------------
        , expectSuccess "Definition with meta symbol"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaSymbolSentenceWithSortParameters
                    (SymbolName "#a") charListMetaSort []
                ]
            )
        , expectSuccess "Meta symbol with one sort parameter"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaSymbolSentenceWithSortParameters
                    (SymbolName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#sv") ]
                ]
            )
        , expectSuccess "Meta symbol with one sort parameter with same name"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaSymbolSentenceWithSortParameters
                    (SymbolName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#a") ]
                ]
            )
        , expectSuccess
            "Meta symbol with one sort parameter with same name as sort"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaSymbolSentenceWithSortParameters
                    (SymbolName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#String") ]
                ]
            )
        , expectSuccess
            "Meta symbol with two sort parameters"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaSymbolSentenceWithSortParameters
                    (SymbolName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName  "#sv1")
                    , sortVariable Meta (SortVariableName  "#sv2")
                    ]
                ]
            )
        ------------------------------------------------------------------
        , expectSuccess "Definition with object symbol"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceSymbolSentence
                    (symbolSentenceWithSortParameters
                        (SymbolName "a") (SortName "s") []
                    )
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Object symbol with one sort parameter"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceSymbolSentence
                    (symbolSentenceWithSortParameters
                        (SymbolName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName "sv") ]
                    )
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Object symbol with one sort parameter with same name"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceSymbolSentence
                    (symbolSentenceWithSortParameters
                        (SymbolName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName  "a") ]
                    )
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess
            "Object symbol with one sort parameter with same name as sort"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceSymbolSentence
                    (symbolSentenceWithSortParameters
                        (SymbolName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName "s") ]
                    )
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectSuccess "Object symbol with two sort parameters"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceSymbolSentence
                    (symbolSentenceWithSortParameters
                        (SymbolName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName  "sv1")
                        , sortVariable Object (SortVariableName  "sv2")
                        ]
                    )
                , simpleSortSentence (SortName "s")
                ]
            )
        ------------------------------------------------------------------
        , expectSuccess "Definition with axiom"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (stringUnifiedPattern "hello") []
                ]
            )
        , expectSuccess "Axiom with one object sort parameter"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (stringUnifiedPattern "hello")
                    [ unifiedSortVariable Object (SortVariableName "sv") ]
                ]
            )
        , expectSuccess "Axiom with one meta sort parameter"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (stringUnifiedPattern "hello")
                    [ unifiedSortVariable Meta (SortVariableName "#sv") ]
                ]
            )
        , expectSuccess "Axiom with two object sort parameters"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (stringUnifiedPattern "hello")
                    [ unifiedSortVariable Object (SortVariableName "sv1")
                    , unifiedSortVariable Object (SortVariableName "sv2")
                    ]
                ]
            )
        , expectSuccess "Axiom with two meta sort parameters"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (stringUnifiedPattern "hello")
                    [ unifiedSortVariable Meta (SortVariableName "#sv1")
                    , unifiedSortVariable Meta (SortVariableName "#sv2")
                    ]
                ]
            )
        , expectSuccess "Axiom with mixed sort parameters"
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (stringUnifiedPattern "hello")
                    [ unifiedSortVariable Object (SortVariableName "sv")
                    , unifiedSortVariable Meta (SortVariableName "#sv")
                    ]
                ]
            )
        ------------------------------------------------------------------
        , expectFailureWithError
            "Sort with two sort parameters with same name"
            (Error
                ["module 'MODULE'", "sort 's' declaration"]
                "Duplicated sort variable: 'sv'."
            )
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ sortSentenceWithSortParameters
                    (SortName "s")
                    [ sortVariable Object (SortVariableName "sv")
                    , sortVariable Object (SortVariableName "sv")
                    ]
                ]
            )
        , expectFailureWithError
            "Meta alias with two sort parameters with same name"
            (Error
                ["module 'MODULE'", "alias '#a' declaration"]
                "Duplicated sort variable: '#sv'."
            )
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaAliasSentenceWithSortParameters
                    (AliasName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#sv")
                    , sortVariable Meta (SortVariableName "#sv")
                    ]
                ]
            )
        , expectFailureWithError
            "Object alias with two sort parameters with same name"
            (Error
                ["module 'MODULE'", "alias 'a' declaration"]
                "Duplicated sort variable: 'sv'."
            )
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceAliasSentence
                    (aliasSentenceWithSortParameters
                        (AliasName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName "sv")
                        , sortVariable Object (SortVariableName "sv")
                        ])
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectFailureWithError
            "Meta symbol with two sort parameters with same name"
            (Error
                ["module 'MODULE'", "symbol '#a' declaration"]
                "Duplicated sort variable: '#sv'."
            )
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ metaSymbolSentenceWithSortParameters
                    (SymbolName "#a")
                    charListMetaSort
                    [ sortVariable Meta (SortVariableName "#sv")
                    , sortVariable Meta (SortVariableName "#sv")
                    ]
                ]
            )
        , expectFailureWithError
            "Object symbol with two sort parameters with same name"
            (Error
                ["module 'MODULE'", "symbol 'a' declaration"]
                "Duplicated sort variable: 'sv'."
            )
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ ObjectSentenceSymbolSentence
                    (symbolSentenceWithSortParameters
                        (SymbolName "a")
                        (SortName "s")
                        [ sortVariable Object (SortVariableName "sv")
                        , sortVariable Object (SortVariableName "sv")
                        ]
                    )
                , simpleSortSentence (SortName "s")
                ]
            )
        , expectFailureWithError
            "Axiom with two object sort parameters with same name"
            (Error
                ["module 'MODULE'", "axiom declaration"]
                "Duplicated sort variable: 'sv'."
            )
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (stringUnifiedPattern "hello")
                    [ unifiedSortVariable Object (SortVariableName "sv")
                    , unifiedSortVariable Object (SortVariableName "sv")
                    ]
                ]
            )
        , expectFailureWithError
            "Axiom with two meta sort parameters with same name"
            (Error
                ["module 'MODULE'", "axiom declaration"]
                "Duplicated sort variable: '#sv'."
            )
            ( simpleDefinitionFromSentences (ModuleName "MODULE")
                [ axiomSentenceWithSortParameters
                    (stringUnifiedPattern "hello")
                    [ unifiedSortVariable Meta (SortVariableName "#sv")
                    , unifiedSortVariable Meta (SortVariableName "#sv")
                    ]
                ]
            )
        ]

