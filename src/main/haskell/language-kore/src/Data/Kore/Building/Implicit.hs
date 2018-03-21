{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Building.Implicit where

import           Data.Kore.AST.Common        (Application (..), Id (..),
                                              Pattern (..), SymbolOrAlias (..))
import           Data.Kore.AST.Kore
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts

data MetaNilSortList = MetaNilSortList
instance AsAst UnifiedPattern MetaNilSortList where
    asAst = MetaPattern . asMetaPattern
instance AsMetaPattern MetaNilSortList where
    asMetaPattern _ =
        ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id "#nilSortList"
                , symbolOrAliasParams = []
                }
            , applicationChildren      = []
            }
instance MetaPattern SortListSort MetaNilSortList where
metaNilSortList :: MetaNilSortList
metaNilSortList = MetaNilSortList
