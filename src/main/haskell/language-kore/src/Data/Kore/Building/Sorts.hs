{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ConstraintKinds #-}
{-|
Module      : Data.Kore.Building.Sorts
Description : Builders for meta sorts and sort variables.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.Building.Sorts where

import           Data.Kore.AST.Common
import           Data.Kore.Building.AsAst
import           Data.Kore.Implicit.ImplicitSorts

type AsSort level = AsAst (Sort level)
type MetaSort = AsSort Meta
type ObjectSort = AsSort Object

data CharSortP level where CharSort :: CharSort
type CharSort = CharSortP Meta
instance AsAst (Sort Meta) CharSort where
    asAst _ = charMetaSort

data CharListSortP level where CharListSort :: CharListSort
type CharListSort = CharListSortP Meta
instance AsAst (Sort Meta) CharListSort where
    asAst _ = charListMetaSort

data PatternSortP level where PatternSort :: PatternSort
type PatternSort = PatternSortP Meta
instance AsAst (Sort Meta) PatternSort where
    asAst _ = patternMetaSort

data PatternListSortP level where PatternListSort :: PatternListSort
type PatternListSort = PatternListSortP Meta
instance AsAst (Sort Meta) PatternListSort where
    asAst _ = patternListMetaSort

data SortSortP level where SortSort :: SortSort
type SortSort = SortSortP Meta
instance AsAst (Sort Meta) SortSort where
    asAst _ = sortMetaSort

data SortListSortP level where SortListSort :: SortListSort
type SortListSort = SortListSortP Meta
instance AsAst (Sort Meta) SortListSort where
    asAst _ = sortListMetaSort

data VariableSortP level where VariableSort :: VariableSort
type VariableSort = VariableSortP Meta
instance AsAst (Sort Meta) VariableSort where
    asAst _ = variableMetaSort

data VariableListSortP level where VariableListSort :: VariableListSort
type VariableListSort = VariableListSortP Meta
instance AsAst (Sort Meta) VariableListSort where
    asAst _ = variableListMetaSort

-- TODO(virgil): rename. Also, it is likely that each variable should have sort
-- distinct type.
data MetaSortVariable1P level where
    MetaSortVariable1 :: !String -> MetaSortVariable1
type MetaSortVariable1 = MetaSortVariable1P Meta
instance AsAst (Sort Meta) MetaSortVariable1 where
    asAst v = SortVariableSort (asMetaSortVariable v)
asMetaSortVariable :: MetaSortVariable1 -> SortVariable Meta
asMetaSortVariable (MetaSortVariable1 name) = SortVariable (Id name)

data ObjectSortVariable1P level where
    ObjectSortVariable1 :: !String -> ObjectSortVariable1
type ObjectSortVariable1 = ObjectSortVariable1P Meta
instance AsAst (Sort Object) ObjectSortVariable1 where
    asAst (ObjectSortVariable1 name) = SortVariableSort (SortVariable (Id name))
