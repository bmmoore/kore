{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Building.Patterns where

import           Data.Kore.AST.Common     (And (..), Equals (..), Exists (..),
                                           Forall (..), Id (..), Implies (..),
                                           Meta, Not (..), Object, Or (..),
                                           Pattern (..), Variable (..))
import           Data.Kore.AST.Kore       (FixedPattern (..), UnifiedPattern)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Sorts

class AsAst UnifiedPattern patt => MetaPattern sort patt where

class AsAst UnifiedPattern patt => AsMetaPattern patt where
    asMetaPattern :: patt -> Pattern Meta Variable UnifiedPattern

class AsAst UnifiedPattern patt => AsObjectPattern patt where
    asObjectPattern :: patt -> Pattern Object Variable UnifiedPattern

class AsAst UnifiedPattern patt => ObjectPattern sort patt where

-------------------------------------

newtype MetaResultSort sort = MetaResultSort sort

data MetaAnd s p1 p2 = MetaAnd
    { metaAndSort   :: s
    , metaAndFirst  :: p1
    , metaAndSecond :: p2
    }
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => AsMetaPattern (MetaAnd s p1 p2)
  where
    asMetaPattern (MetaAnd sort first second) =
        AndPattern (And (asAst sort) (asAst first) (asAst second))
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => AsAst UnifiedPattern (MetaAnd s p1 p2)
  where
    asAst = MetaPattern . asMetaPattern
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => MetaPattern s (MetaAnd s p1 p2) where
instance (MetaPattern PatternSort p1, MetaPattern PatternSort p2)
    => ObjectPattern a (MetaAnd PatternSort p1 p2) where
metaAnd
    :: (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => s -> p1 -> p2 -> MetaAnd s p1 p2
metaAnd = MetaAnd

data MetaEquals s1 s2 p1 p2 = MetaEquals
    { metaEqualsResultSort  :: MetaResultSort s1
    , metaEqualsOperandSort :: s2
    , metaEqualsFirst       :: p1
    , metaEqualsSecond      :: p2
    }
instance (MetaSort s1, MetaSort s2, MetaPattern s2 p1, MetaPattern s2 p2)
    => AsMetaPattern (MetaEquals s1 s2 p1 p2)
  where
    asMetaPattern
        (MetaEquals (MetaResultSort resultSort) operandSort first second)
      =
        EqualsPattern Equals
            { equalsOperandSort = asAst operandSort
            , equalsResultSort  = asAst resultSort
            , equalsFirst       = asAst first
            , equalsSecond      = asAst second
            }
instance (MetaSort s1, MetaSort s2, MetaPattern s2 p1, MetaPattern s2 p2)
    => AsAst UnifiedPattern (MetaEquals s1 s2 p1 p2)
  where
    asAst = MetaPattern . asMetaPattern
instance (MetaSort s1, MetaSort s2, MetaPattern s2 p1, MetaPattern s2 p2)
    => MetaPattern s1 (MetaEquals s1 s2 p1 p2) where
instance (MetaSort s2, MetaPattern s2 p1, MetaPattern s2 p2)
    => ObjectPattern a (MetaEquals PatternSort s2 p1 p2) where
metaEquals
    :: (MetaSort s1, MetaSort s2, MetaPattern s2 p1, MetaPattern s2 p2)
    => MetaResultSort s1 -> s2 -> p1 -> p2 -> MetaEquals s1 s2 p1 p2
metaEquals = MetaEquals

data MetaImplies s p1 p2 = MetaImplies
    { metaImpliesSort   :: s
    , metaImpliesFirst  :: p1
    , metaImpliesSecond :: p2
    }
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => AsMetaPattern (MetaImplies s p1 p2)
  where
    asMetaPattern (MetaImplies sort first second) =
        ImpliesPattern (Implies (asAst sort) (asAst first) (asAst second))
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => AsAst UnifiedPattern (MetaImplies s p1 p2)
  where
    asAst = MetaPattern . asMetaPattern
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => MetaPattern s (MetaImplies s p1 p2) where
instance (MetaPattern PatternSort p1, MetaPattern PatternSort p2)
    => ObjectPattern a (MetaImplies PatternSort p1 p2) where
metaImplies
    :: (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => s -> p1 -> p2 -> MetaImplies s p1 p2
metaImplies = MetaImplies

data MetaNot s p1 = MetaNot
    { metaNotSort  :: s
    , metaNotChild :: p1
    }
instance (MetaSort s, MetaPattern s p1)
    => AsMetaPattern (MetaNot s p1)
  where
    asMetaPattern (MetaNot sort child) =
        NotPattern (Not (asAst sort) (asAst child))
instance (MetaSort s, MetaPattern s p1)
    => AsAst UnifiedPattern (MetaNot s p1)
  where
    asAst = MetaPattern . asMetaPattern
instance (MetaSort s, MetaPattern s p1)
    => MetaPattern s (MetaNot s p1) where
instance (MetaPattern PatternSort p1)
    => ObjectPattern a (MetaNot PatternSort p1) where
metaNot
    :: (MetaSort s, MetaPattern s p1)
    => s -> p1 -> MetaNot s p1
metaNot = MetaNot

data MetaOr s p1 p2 = MetaOr
    { metaOrSort   :: s
    , metaOrFirst  :: p1
    , metaOrSecond :: p2
    }
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => AsMetaPattern (MetaOr s p1 p2)
  where
    asMetaPattern (MetaOr s p1 p2) =
        OrPattern (Or (asAst s) (asAst p1) (asAst p2))
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => AsAst UnifiedPattern (MetaOr s p1 p2)
  where
    asAst = MetaPattern . asMetaPattern
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => MetaPattern s (MetaOr s p1 p2) where
instance (MetaPattern PatternSort p1, MetaPattern PatternSort p2)
    => ObjectPattern a (MetaOr PatternSort p1 p2) where
metaOr
    :: (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => s -> p1 -> p2 -> MetaOr s p1 p2
metaOr = MetaOr

data MetaVariable s = MetaVariable
    { metaVariableName :: String
    , metaVariableSort :: s
    }
instance MetaSort s => AsMetaPattern (MetaVariable s)
  where
    asMetaPattern var =
        VariablePattern (asVariable var)
instance MetaSort s => AsAst UnifiedPattern (MetaVariable s)
  where
    asAst = MetaPattern . asMetaPattern
instance MetaSort s => MetaPattern s (MetaVariable s) where
instance ObjectPattern a (MetaVariable PatternSort) where
metaVariable
    :: MetaSort s
    => String -> s -> MetaVariable s
metaVariable = MetaVariable
asVariable :: MetaSort s => MetaVariable s -> Variable Meta
asVariable (MetaVariable name s) = Variable (Id name) (asAst s)

data MetaExists s v p = MetaExists
    { metaExistsSort     :: s
    , metaExistsVariable :: v
    , metaExistsPattern  :: p
    }
instance (MetaSort s, MetaSort sv, MetaPattern s p)
    => AsMetaPattern (MetaExists s (MetaVariable sv) p)
  where
    asMetaPattern (MetaExists s var patt) =
        ExistsPattern (Exists (asAst s) (asVariable var) (asAst patt))
instance (MetaSort s, MetaSort sv, MetaPattern s p)
    => AsAst UnifiedPattern (MetaExists s (MetaVariable sv) p)
  where
    asAst = MetaPattern . asMetaPattern
instance (MetaSort s, MetaSort sv, MetaPattern s p)
    => MetaPattern s (MetaExists s (MetaVariable sv) p) where
instance (MetaSort sv, MetaPattern PatternSort p)
    => ObjectPattern a (MetaExists PatternSort (MetaVariable sv) p) where
metaExists
    :: (MetaSort s, MetaSort sv, MetaPattern s p)
    => s -> MetaVariable sv -> p -> MetaExists s (MetaVariable sv) p
metaExists = MetaExists

data MetaForall s v p = MetaForall
    { metaForallSort     :: s
    , metaForallVariable :: v
    , metaForallPattern  :: p
    }
instance (MetaSort s, MetaSort sv, MetaPattern s p)
    => AsMetaPattern (MetaForall s (MetaVariable sv) p)
  where
    asMetaPattern (MetaForall s var patt) =
        ForallPattern (Forall (asAst s) (asVariable var) (asAst patt))
instance (MetaSort s, MetaSort sv, MetaPattern s p)
    => AsAst UnifiedPattern (MetaForall s (MetaVariable sv) p)
  where
    asAst = MetaPattern . asMetaPattern
instance (MetaSort s, MetaSort sv, MetaPattern s p)
    => MetaPattern s (MetaForall s (MetaVariable sv) p) where
instance (MetaSort sv, MetaPattern PatternSort p)
    => ObjectPattern a (MetaForall PatternSort (MetaVariable sv) p) where
metaForall
    :: (MetaSort s, MetaSort sv, MetaPattern s p)
    => s -> MetaVariable sv -> p -> MetaForall s (MetaVariable sv) p
metaForall = MetaForall

data ObjectAnd s p1 p2 = ObjectAnd
    { objectAndSort   :: s
    , objectAndFirst  :: p1
    , objectAndSecond :: p2
    }
instance (ObjectSort s, ObjectPattern s p1, ObjectPattern s p2)
    => AsObjectPattern (ObjectAnd s p1 p2) where
    asObjectPattern (ObjectAnd s p1 p2) =
        AndPattern (And (asAst s) (asAst p1) (asAst p2))
instance (ObjectSort s, ObjectPattern s p1, ObjectPattern s p2)
    => AsAst UnifiedPattern (ObjectAnd s p1 p2)
  where
    asAst = ObjectPattern . asObjectPattern
instance (ObjectSort s, ObjectPattern s p1, ObjectPattern s p2)
    => ObjectPattern s (ObjectAnd s p1 p2) where
instance (ObjectSort s, ObjectPattern s p1, ObjectPattern s p2)
    => MetaPattern PatternSort (ObjectAnd s p1 p2) where
objectAnd
    :: (ObjectSort s, ObjectPattern s p1, ObjectPattern s p2)
    => s -> p1 -> p2 -> ObjectAnd s p1 p2
objectAnd = ObjectAnd
