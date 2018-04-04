{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-|
Module      : Data.Kore.Building.Patterns
Description : Builders for the standard Kore patterns, without 'Application'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.Building.Patterns where

import           Data.Kore.AST.Common     (And (..), Bottom (..), Ceil (..),
                                           CharLiteral (..), DomainValue (..),
                                           Equals (..), Exists (..), Floor (..),
                                           Forall (..), Id (..), Iff (..),
                                           Implies (..), In (..), Meta,
                                           Next (..), Not (..), Object, Or (..),
                                           Pattern (..), Rewrites (..),
                                           StringLiteral (..), Top (..),
                                           Variable (..))
import           Data.Kore.AST.Kore       (FixedPattern (..), UnifiedPattern)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Sorts

{-| When defining new patterns (e.g. for new symbols and aliases),
users are expected to instantiate either
`ProperMetaPattern` or `ProperObjectPattern`, the other derivations
(e.g. for `MetaPattern` and `AsAst`) being inferred automatically.
-}
class ProperMetaPattern sort patt where
    asProperMetaPattern
        :: patt sort Meta -> Pattern Meta Variable UnifiedPattern
class ProperObjectPattern sort patt where
    asProperObjectPattern
        :: patt sort Object -> Pattern Object Variable UnifiedPattern

class AsAst UnifiedPattern patt => AsMetaPattern patt where
    asMetaPattern :: patt -> Pattern Meta Variable UnifiedPattern
class AsAst UnifiedPattern patt => AsObjectPattern patt where
    asObjectPattern :: patt -> Pattern Object Variable UnifiedPattern

class AsAst UnifiedPattern patt => ObjectPattern sort patt where
class AsAst UnifiedPattern patt => MetaPattern sort patt where

-------------------------------------

instance ProperMetaPattern sort patt => AsAst UnifiedPattern (patt sort Meta)
  where
    asAst = MetaPattern . asProperMetaPattern
instance ProperMetaPattern sort patt => MetaPattern sort (patt sort Meta) where
instance ProperMetaPattern sort patt => AsMetaPattern (patt sort Meta) where
    asMetaPattern = asProperMetaPattern
instance ProperMetaPattern PatternSort patt
    => ObjectPattern a (patt PatternSort Meta) where

instance ProperObjectPattern sort patt
    => AsAst UnifiedPattern (patt sort Object)
  where
    asAst = ObjectPattern . asProperObjectPattern
instance ProperObjectPattern sort patt
    => ObjectPattern sort (patt sort Object)
  where
instance ProperObjectPattern sort patt
    => AsObjectPattern (patt sort Object)
  where
    asObjectPattern = asProperObjectPattern
instance (ProperObjectPattern sort patt)
    => MetaPattern PatternSort (patt sort Object)
  where

-------------------------------------

newtype ResultSort sort = ResultSort sort
newtype ContainedChild patt = ContainedChild patt

-------------------------------------

data PatternAnd pattern1 pattern2 sort level = PatternAnd
    { patternAndSort   :: sort
    , patternAndFirst  :: pattern1
    , patternAndSecond :: pattern2
    }

type MetaAnd pattern1 pattern2 sort = PatternAnd pattern1 pattern2 sort Meta
instance (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => ProperMetaPattern sort (PatternAnd pattern1 pattern2)
  where
    asProperMetaPattern (PatternAnd sort first second) =
        AndPattern (And (asAst sort) (asAst first) (asAst second))
metaAnd
    :: (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> MetaAnd pattern1 pattern2 sort
metaAnd = PatternAnd

type ObjectAnd pattern1 pattern2 sort = PatternAnd pattern1 pattern2 sort Object
instance
    (ObjectSort sort, ObjectPattern sort pattern1, ObjectPattern sort pattern2)
    => ProperObjectPattern sort (PatternAnd pattern1 pattern2)
  where
    asProperObjectPattern (PatternAnd sort first second) =
        AndPattern (And (asAst sort) (asAst first) (asAst second))
objectAnd
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> ObjectAnd pattern1 pattern2 sort
objectAnd = PatternAnd

-------------------------------------

newtype PatternBottom sort level = PatternBottom
    { patternBottomSort :: sort }

type MetaBottom sort = PatternBottom sort Meta
instance MetaSort sort => ProperMetaPattern sort PatternBottom where
    asProperMetaPattern (PatternBottom sort) =
        BottomPattern (Bottom (asAst sort))
metaBottom :: (MetaSort sort) => sort -> MetaBottom sort
metaBottom = PatternBottom

type ObjectBottom sort = PatternBottom sort Object
instance ObjectSort sort => ProperObjectPattern sort PatternBottom
  where
    asProperObjectPattern (PatternBottom sort) =
        BottomPattern (Bottom (asAst sort))
objectBottom :: ObjectSort sort => sort -> ObjectBottom sort
objectBottom = PatternBottom

-------------------------------------

data PatternCeil childSort child resultSort level = PatternCeil
    { patternCeilResultSort  :: ResultSort resultSort
    , patternCeilOperandSort :: childSort
    , patternCeilChild       :: child
    }

type MetaCeil childSort child resultSort =
    PatternCeil childSort child resultSort Meta
instance
    ( MetaSort resultSort
    , MetaSort childSort
    , MetaPattern childSort child)
    => ProperMetaPattern resultSort (PatternCeil childSort child)
  where
    asProperMetaPattern
        (PatternCeil (ResultSort resultSort) operandSort child)
      =
        CeilPattern Ceil
            { ceilOperandSort = asAst operandSort
            , ceilResultSort  = asAst resultSort
            , ceilChild       = asAst child
            }
metaCeil
    ::  ( MetaSort resultSort
        , MetaSort childSort
        , MetaPattern childSort child
        )
    => ResultSort resultSort
    -> childSort
    -> child
    -> MetaCeil childSort child resultSort
metaCeil = PatternCeil

type ObjectCeil childSort child resultSort =
    PatternCeil childSort child resultSort Object
instance
    ( ObjectSort resultSort
    , ObjectSort childSort
    , ObjectPattern childSort child)
    => ProperObjectPattern resultSort (PatternCeil childSort child)
  where
    asProperObjectPattern
        (PatternCeil (ResultSort resultSort) operandSort child)
      =
        CeilPattern Ceil
            { ceilOperandSort = asAst operandSort
            , ceilResultSort  = asAst resultSort
            , ceilChild       = asAst child
            }
objectCeil
    ::  ( ObjectSort resultSort
        , ObjectSort childSort
        , ObjectPattern childSort child
        )
    => ResultSort resultSort
    -> childSort
    -> child
    -> ObjectCeil childSort child resultSort
objectCeil = PatternCeil

-------------------------------------

data PatternDomainValue pattern1 sort level = PatternDomainValue
    { patternDomainValueSort  :: sort
    , patternDomainValueChild :: pattern1
    }

type ObjectDomainValue pattern1 sort = PatternDomainValue pattern1 sort Object
instance
    (ObjectSort sort, MetaPattern CharListSort pattern1)
    => ProperObjectPattern sort (PatternDomainValue pattern1)
  where
    asProperObjectPattern (PatternDomainValue sort child) =
        DomainValuePattern (DomainValue (asAst sort) (asAst child))
objectDomainValue
    :: (ObjectSort sort, MetaPattern CharListSort pattern1)
    => sort -> pattern1 -> ObjectDomainValue pattern1 sort
objectDomainValue = PatternDomainValue

-------------------------------------

data PatternEquals childSort pattern1 pattern2 resultSort level = PatternEquals
    { patternEqualsResultSort  :: ResultSort resultSort
    , patternEqualsOperandSort :: childSort
    , patternEqualsFirst       :: pattern1
    , patternEqualsSecond      :: pattern2
    }

type MetaEquals childSort pattern1 pattern2 resultSort =
    PatternEquals childSort pattern1 pattern2 resultSort Meta
instance
    ( MetaSort resultSort
    , MetaSort childSort
    , MetaPattern childSort pattern1
    , MetaPattern childSort pattern2)
    => ProperMetaPattern resultSort (PatternEquals childSort pattern1 pattern2)
  where
    asProperMetaPattern
        (PatternEquals (ResultSort resultSort) operandSort first second)
      =
        EqualsPattern Equals
            { equalsOperandSort = asAst operandSort
            , equalsResultSort  = asAst resultSort
            , equalsFirst       = asAst first
            , equalsSecond      = asAst second
            }
metaEquals
    ::  ( MetaSort resultSort
        , MetaSort childSort
        , MetaPattern childSort pattern1
        , MetaPattern childSort pattern2
        )
    => ResultSort resultSort
    -> childSort
    -> pattern1
    -> pattern2
    -> MetaEquals childSort pattern1 pattern2 resultSort
metaEquals = PatternEquals

type ObjectEquals childSort pattern1 pattern2 resultSort =
    PatternEquals childSort pattern1 pattern2 resultSort Object
instance
    ( ObjectSort resultSort
    , ObjectSort childSort
    , ObjectPattern childSort pattern1
    , ObjectPattern childSort pattern2)
    => ProperObjectPattern
        resultSort
        (PatternEquals childSort pattern1 pattern2)
  where
    asProperObjectPattern
        (PatternEquals (ResultSort resultSort) operandSort first second)
      =
        EqualsPattern Equals
            { equalsOperandSort = asAst operandSort
            , equalsResultSort  = asAst resultSort
            , equalsFirst       = asAst first
            , equalsSecond      = asAst second
            }
objectEquals
    ::  ( ObjectSort resultSort
        , ObjectSort childSort
        , ObjectPattern childSort pattern1
        , ObjectPattern childSort pattern2
        )
    => ResultSort resultSort
    -> childSort
    -> pattern1
    -> pattern2
    -> ObjectEquals childSort pattern1 pattern2 resultSort
objectEquals = PatternEquals

-------------------------------------

data PatternExists variable pattern1 sort level = PatternExists
    { metaExistsSort     :: sort
    , metaExistsVariable :: variable
    , metaExistsPattern  :: pattern1
    }

type MetaExists variable pattern1 sort =
    PatternExists variable pattern1 sort Meta
instance (MetaSort sort, MetaSort sv, MetaPattern sort pattern1)
    => ProperMetaPattern sort (PatternExists (MetaVariable sv) pattern1)
  where
    asProperMetaPattern (PatternExists sort var patt) =
        ExistsPattern (Exists (asAst sort) (asMetaVariable var) (asAst patt))
metaExists
    :: (MetaSort sort, MetaSort sv, MetaPattern sort pattern1)
    => sort
    -> MetaVariable sv
    -> pattern1
    -> MetaExists (MetaVariable sv) pattern1 sort
metaExists = PatternExists

type ObjectExists variable pattern1 sort =
    PatternExists variable pattern1 sort Object
instance (ObjectSort sort, ObjectSort sv, ObjectPattern sort pattern1)
    => ProperObjectPattern sort (PatternExists (ObjectVariable sv) pattern1)
  where
    asProperObjectPattern (PatternExists sort var patt) =
        ExistsPattern (Exists (asAst sort) (asObjectVariable var) (asAst patt))
objectExists
    :: (ObjectSort sort, ObjectSort sv, ObjectPattern sort pattern1)
    => sort
    -> ObjectVariable sv
    -> pattern1
    -> ObjectExists (ObjectVariable sv) pattern1 sort
objectExists = PatternExists

-------------------------------------

data PatternFloor childSort child resultSort level = PatternFloor
    { patternFloorResultSort  :: ResultSort resultSort
    , patternFloorOperandSort :: childSort
    , patternFloorChild       :: child
    }

type MetaFloor childSort child resultSort =
    PatternFloor childSort child resultSort Meta
instance
    ( MetaSort resultSort
    , MetaSort childSort
    , MetaPattern childSort child)
    => ProperMetaPattern resultSort (PatternFloor childSort child)
  where
    asProperMetaPattern
        (PatternFloor (ResultSort resultSort) operandSort child)
      =
        FloorPattern Floor
            { floorOperandSort = asAst operandSort
            , floorResultSort  = asAst resultSort
            , floorChild       = asAst child
            }
metaFloor
    ::  ( MetaSort resultSort
        , MetaSort childSort
        , MetaPattern childSort child
        )
    => ResultSort resultSort
    -> childSort
    -> child
    -> MetaFloor childSort child resultSort
metaFloor = PatternFloor

type ObjectFloor childSort child resultSort =
    PatternFloor childSort child resultSort Object
instance
    ( ObjectSort resultSort
    , ObjectSort childSort
    , ObjectPattern childSort child)
    => ProperObjectPattern resultSort (PatternFloor childSort child)
  where
    asProperObjectPattern
        (PatternFloor (ResultSort resultSort) operandSort child)
      =
        FloorPattern Floor
            { floorOperandSort = asAst operandSort
            , floorResultSort  = asAst resultSort
            , floorChild       = asAst child
            }
objectFloor
    ::  ( ObjectSort resultSort
        , ObjectSort childSort
        , ObjectPattern childSort child
        )
    => ResultSort resultSort
    -> childSort
    -> child
    -> ObjectFloor childSort child resultSort
objectFloor = PatternFloor

-------------------------------------

data PatternForall variable pattern1 sort level = PatternForall
    { patternForallSort     :: sort
    , patternForallVariable :: variable
    , patternForallPattern  :: pattern1
    }

type MetaForall variable pattern1 sort =
    PatternForall variable pattern1 sort Meta
instance (MetaSort sort, MetaSort variableSort, MetaPattern sort pattern1)
    => ProperMetaPattern
        sort
        (PatternForall (MetaVariable variableSort) pattern1)
  where
    asProperMetaPattern (PatternForall sort var patt) =
        ForallPattern (Forall (asAst sort) (asMetaVariable var) (asAst patt))
metaForall
    :: (MetaSort sort, MetaSort variableSort, MetaPattern sort pattern1)
    => sort
    -> MetaVariable variableSort
    -> pattern1
    -> MetaForall (MetaVariable variableSort) pattern1 sort
metaForall = PatternForall

type ObjectForall variable pattern1 sort =
    PatternForall variable pattern1 sort Object
instance (ObjectSort sort, ObjectSort variableSort, ObjectPattern sort pattern1)
    => ProperObjectPattern
        sort
        (PatternForall (ObjectVariable variableSort) pattern1)
  where
    asProperObjectPattern (PatternForall sort var patt) =
        ForallPattern (Forall (asAst sort) (asObjectVariable var) (asAst patt))
objectForall
    :: (ObjectSort sort, ObjectSort variableSort, ObjectPattern sort pattern1)
    => sort
    -> ObjectVariable variableSort
    -> pattern1
    -> ObjectForall (ObjectVariable variableSort) pattern1 sort
objectForall = PatternForall

-------------------------------------

data PatternIff pattern1 pattern2 sort level = PatternIff
    { patternIffSort   :: sort
    , patternIffFirst  :: pattern1
    , patternIffSecond :: pattern2
    }

type MetaIff pattern1 pattern2 sort = PatternIff pattern1 pattern2 sort Meta
instance (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => ProperMetaPattern sort (PatternIff pattern1 pattern2)
  where
    asProperMetaPattern (PatternIff sort first second) =
        IffPattern (Iff (asAst sort) (asAst first) (asAst second))
metaIff
    :: (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> MetaIff pattern1 pattern2 sort
metaIff = PatternIff

type ObjectIff pattern1 pattern2 sort = PatternIff pattern1 pattern2 sort Object
instance
    (ObjectSort sort, ObjectPattern sort pattern1, ObjectPattern sort pattern2)
    => ProperObjectPattern sort (PatternIff pattern1 pattern2)
  where
    asProperObjectPattern (PatternIff sort first second) =
        IffPattern (Iff (asAst sort) (asAst first) (asAst second))
objectIff
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2
        )
    => sort -> pattern1 -> pattern2 -> ObjectIff pattern1 pattern2 sort
objectIff = PatternIff

-------------------------------------

data PatternImplies pattern1 pattern2 sort level = PatternImplies
    { patternImpliesSort   :: sort
    , patternImpliesFirst  :: pattern1
    , patternImpliesSecond :: pattern2
    }

type MetaImplies pattern1 pattern2 sort =
    PatternImplies pattern1 pattern2 sort Meta
instance (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => ProperMetaPattern sort (PatternImplies pattern1 pattern2)
  where
    asProperMetaPattern (PatternImplies sort first second) =
        ImpliesPattern (Implies (asAst sort) (asAst first) (asAst second))
metaImplies
    :: (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> MetaImplies pattern1 pattern2 sort
metaImplies = PatternImplies

type ObjectImplies pattern1 pattern2 sort =
    PatternImplies pattern1 pattern2 sort Object
instance
    (ObjectSort sort, ObjectPattern sort pattern1, ObjectPattern sort pattern2)
    => ProperObjectPattern sort (PatternImplies pattern1 pattern2)
  where
    asProperObjectPattern (PatternImplies sort first second) =
        ImpliesPattern (Implies (asAst sort) (asAst first) (asAst second))
objectImplies
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2
        )
    => sort -> pattern1 -> pattern2 -> ObjectImplies pattern1 pattern2 sort
objectImplies = PatternImplies

-------------------------------------

data PatternIn childSort pattern1 pattern2 resultSort level = PatternIn
    { patternInResultSort      :: ResultSort resultSort
    , patternInOperandSort     :: childSort
    , patternInContainedChild  :: ContainedChild pattern1
    , patternInContainingChild :: pattern2
    }

type MetaIn childSort pattern1 pattern2 resultSort =
    PatternIn childSort pattern1 pattern2 resultSort Meta
instance
    ( MetaSort resultSort
    , MetaSort childSort
    , MetaPattern childSort pattern1
    , MetaPattern childSort pattern2)
    => ProperMetaPattern resultSort (PatternIn childSort pattern1 pattern2)
  where
    asProperMetaPattern
        (PatternIn
            (ResultSort resultSort) operandSort (ContainedChild first) second
        )
      =
        InPattern In
            { inOperandSort = asAst operandSort
            , inResultSort  = asAst resultSort
            , inContainedChild       = asAst first
            , inContainingChild      = asAst second
            }
metaIn
    ::  ( MetaSort resultSort
        , MetaSort childSort
        , MetaPattern childSort pattern1
        , MetaPattern childSort pattern2
        )
    => ResultSort resultSort
    -> childSort
    -> ContainedChild pattern1
    -> pattern2
    -> MetaIn childSort pattern1 pattern2 resultSort
metaIn = PatternIn

type ObjectIn childSort pattern1 pattern2 resultSort =
    PatternIn childSort pattern1 pattern2 resultSort Object
instance
    ( ObjectSort resultSort
    , ObjectSort childSort
    , ObjectPattern childSort pattern1
    , ObjectPattern childSort pattern2)
    => ProperObjectPattern resultSort (PatternIn childSort pattern1 pattern2)
  where
    asProperObjectPattern
        (PatternIn
            (ResultSort resultSort) operandSort (ContainedChild first) second
        )
      =
        InPattern In
            { inOperandSort = asAst operandSort
            , inResultSort  = asAst resultSort
            , inContainedChild       = asAst first
            , inContainingChild      = asAst second
            }
objectIn
    ::  ( ObjectSort resultSort
        , ObjectSort childSort
        , ObjectPattern childSort pattern1
        , ObjectPattern childSort pattern2
        )
    => ResultSort resultSort
    -> childSort
    -> ContainedChild pattern1
    -> pattern2
    -> ObjectIn childSort pattern1 pattern2 resultSort
objectIn = PatternIn

-------------------------------------

data PatternNext pattern1 sort level = PatternNext
    { patternNextSort  :: sort
    , patternNextChild :: pattern1
    }

type ObjectNext pattern1 sort = PatternNext pattern1 sort Object
instance (ObjectSort sort, ObjectPattern sort pattern1)
    => ProperObjectPattern sort (PatternNext pattern1)
  where
    asProperObjectPattern (PatternNext sort child) =
        NextPattern (Next (asAst sort) (asAst child))
objectNext
    :: (ObjectSort sort, ObjectPattern sort pattern1)
    => sort -> pattern1 -> ObjectNext pattern1 sort
objectNext = PatternNext

-------------------------------------

data PatternNot pattern1 sort level = PatternNot
    { patternNotSort  :: sort
    , patternNotChild :: pattern1
    }

type MetaNot pattern1 sort = PatternNot pattern1 sort Meta
instance (MetaSort sort, MetaPattern sort pattern1)
    => ProperMetaPattern sort (PatternNot pattern1)
  where
    asProperMetaPattern (PatternNot sort child) =
        NotPattern (Not (asAst sort) (asAst child))
metaNot
    :: (MetaSort sort, MetaPattern sort pattern1)
    => sort -> pattern1 -> MetaNot pattern1 sort
metaNot = PatternNot

type ObjectNot pattern1 sort = PatternNot pattern1 sort Object
instance (ObjectSort sort, ObjectPattern sort pattern1)
    => ProperObjectPattern sort (PatternNot pattern1)
  where
    asProperObjectPattern (PatternNot sort child) =
        NotPattern (Not (asAst sort) (asAst child))
objectNot
    :: (ObjectSort sort, ObjectPattern sort pattern1)
    => sort -> pattern1 -> ObjectNot pattern1 sort
objectNot = PatternNot

-------------------------------------

data PatternOr pattern1 pattern2 sort level = PatternOr
    { patternOrSort   :: sort
    , patternOrFirst  :: pattern1
    , patternOrSecond :: pattern2
    }

type MetaOr pattern1 pattern2 sort = PatternOr pattern1 pattern2 sort Meta
instance (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => ProperMetaPattern sort (PatternOr pattern1 pattern2)
  where
    asProperMetaPattern (PatternOr sort pattern1 pattern2) =
        OrPattern (Or (asAst sort) (asAst pattern1) (asAst pattern2))
metaOr
    :: (MetaSort sort, MetaPattern sort pattern1, MetaPattern sort pattern2)
    => sort -> pattern1 -> pattern2 -> MetaOr pattern1 pattern2 sort
metaOr = PatternOr

type ObjectOr pattern1 pattern2 sort = PatternOr pattern1 pattern2 sort Object
instance
    (ObjectSort sort, ObjectPattern sort pattern1, ObjectPattern sort pattern2)
    => ProperObjectPattern sort (PatternOr pattern1 pattern2)
  where
    asProperObjectPattern (PatternOr sort pattern1 pattern2) =
        OrPattern (Or (asAst sort) (asAst pattern1) (asAst pattern2))
objectOr
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2
        )
    => sort -> pattern1 -> pattern2 -> ObjectOr pattern1 pattern2 sort
objectOr = PatternOr

-------------------------------------

data PatternRewrites pattern1 pattern2 sort level = PatternRewrites
    { patternRewritesSort   :: sort
    , patternRewritesFirst  :: pattern1
    , patternRewritesSecond :: pattern2
    }

type ObjectRewrites pattern1 pattern2 sort =
    PatternRewrites pattern1 pattern2 sort Object
instance
    ( ObjectSort sort
    , ObjectPattern sort pattern1
    , ObjectPattern sort pattern2
    )
    => ProperObjectPattern sort (PatternRewrites pattern1 pattern2)
  where
    asProperObjectPattern (PatternRewrites sort pattern1 pattern2) =
        RewritesPattern
            (Rewrites (asAst sort) (asAst pattern1) (asAst pattern2))
objectRewrites
    ::  ( ObjectSort sort
        , ObjectPattern sort pattern1
        , ObjectPattern sort pattern2
        )
    => sort -> pattern1 -> pattern2 -> ObjectRewrites pattern1 pattern2 sort
objectRewrites = PatternRewrites

-------------------------------------

newtype PatternTop sort level = PatternTop
    { patternTopSort :: sort }

type MetaTop sort = PatternTop sort Meta
instance MetaSort sort => ProperMetaPattern sort PatternTop where
    asProperMetaPattern (PatternTop sort) =
        TopPattern (Top (asAst sort))
metaTop :: (MetaSort sort) => sort -> MetaTop sort
metaTop = PatternTop

type ObjectTop sort = PatternTop sort Object
instance ObjectSort sort => ProperObjectPattern sort PatternTop
  where
    asProperObjectPattern (PatternTop sort) =
        TopPattern (Top (asAst sort))
objectTop :: ObjectSort sort => sort -> ObjectTop sort
objectTop = PatternTop

-------------------------------------

newtype PatternString sort level = PatternString
    { patternStringValue :: String }

type MetaString = PatternString CharListSort Meta
instance ProperMetaPattern CharListSort PatternString where
    asProperMetaPattern (PatternString value) =
        StringLiteralPattern (StringLiteral value)
metaString :: String -> MetaString
metaString = PatternString

-------------------------------------

newtype PatternChar sort level = PatternChar
    { patternCharValue :: Char }

type MetaChar = PatternChar CharListSort Meta
instance ProperMetaPattern CharListSort PatternChar where
    asProperMetaPattern (PatternChar value) =
        CharLiteralPattern (CharLiteral value)
metaChar :: Char -> MetaChar
metaChar = PatternChar

-------------------------------------

data PatternVariable sort level = PatternVariable
    { metaVariableName :: !String
    , metaVariableSort :: !sort
    }

type MetaVariable sort = PatternVariable sort Meta
instance MetaSort sort => ProperMetaPattern sort PatternVariable
  where
    asProperMetaPattern var =
        VariablePattern (asMetaVariable var)
metaVariable
    :: MetaSort sort
    => String -> sort -> MetaVariable sort
metaVariable = PatternVariable
asMetaVariable :: MetaSort sort => MetaVariable sort -> Variable Meta
asMetaVariable (PatternVariable name sort) = Variable (Id name) (asAst sort)

type ObjectVariable sort = PatternVariable sort Object
instance ObjectSort sort => ProperObjectPattern sort PatternVariable
  where
    asProperObjectPattern var =
        VariablePattern (asObjectVariable var)
objectVariable
    :: ObjectSort sort
    => String -> sort -> ObjectVariable sort
objectVariable = PatternVariable
asObjectVariable :: ObjectSort sort => ObjectVariable sort -> Variable Object
asObjectVariable (PatternVariable name sort) = Variable (Id name) (asAst sort)


