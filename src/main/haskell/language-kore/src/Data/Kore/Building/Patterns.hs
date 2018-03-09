{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Building.Patterns where

import           Data.Kore.AST.Common     (And (..), Id (..), Implies (..),
                                           Meta, Object, Or (..), Pattern (..),
                                           Variable (..))
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
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => ObjectPattern a (MetaAnd s p1 p2) where
metaAnd
    :: (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => s -> p1 -> p2 -> MetaAnd s p1 p2
metaAnd = MetaAnd

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
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => ObjectPattern a (MetaImplies s p1 p2) where
metaImplies
    :: (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => s -> p1 -> p2 -> MetaImplies s p1 p2
metaImplies = MetaImplies

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
instance (MetaSort s, MetaPattern s p1, MetaPattern s p2)
    => ObjectPattern a (MetaOr s p1 p2) where
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
    asMetaPattern (MetaVariable name s) =
        VariablePattern (Variable (Id name) (asAst s))
instance MetaSort s => AsAst UnifiedPattern (MetaVariable s)
  where
    asAst = MetaPattern . asMetaPattern
instance MetaSort s => MetaPattern s (MetaVariable s) where
instance MetaSort s => ObjectPattern a (MetaVariable s) where
metaVariable
    :: MetaSort s
    => String -> s -> MetaVariable s
metaVariable = MetaVariable

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
