{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Building.Sorts where

import           Data.Kore.AST.Common
import           Data.Kore.Building.AsAst
import           Data.Kore.Implicit.ImplicitSorts

class AsAst (Sort Meta) a => MetaSort a where

class AsAst (Sort Object) a => ObjectSort a where

data CharSort = CharSort
instance AsAst (Sort Meta) CharSort where
    asAst _ = charMetaSort
instance MetaSort CharSort where

data CharListSort = CharListSort
instance AsAst (Sort Meta) CharListSort where
    asAst _ = charListMetaSort
instance MetaSort CharListSort where

data PatternSort = PatternSort
instance AsAst (Sort Meta) PatternSort where
    asAst _ = patternMetaSort
instance MetaSort PatternSort where

data PatternListSort = PatternListSort
instance AsAst (Sort Meta) PatternListSort where
    asAst _ = patternListMetaSort
instance MetaSort PatternListSort where

data SortSort = SortSort
instance AsAst (Sort Meta) SortSort where
    asAst _ = sortMetaSort
instance MetaSort SortSort where

data SortListSort = SortListSort
instance AsAst (Sort Meta) SortListSort where
    asAst _ = sortListMetaSort
instance MetaSort SortListSort where

data VariableSort = VariableSort
instance AsAst (Sort Meta) VariableSort where
    asAst _ = variableMetaSort
instance MetaSort VariableSort where

data VariableListSort = VariableListSort
instance AsAst (Sort Meta) VariableListSort where
    asAst _ = variableListMetaSort
instance MetaSort VariableListSort where

-- TODO: rename.
newtype MetaSortVariable1 = MetaSortVariable1 String
instance AsAst (Sort Meta) MetaSortVariable1 where
    asAst (MetaSortVariable1 name) = SortVariableSort (SortVariable (Id name))
instance MetaSort MetaSortVariable1 where

newtype ObjectSortVariable1 = ObjectSortVariable1 String
instance AsAst (Sort Object) ObjectSortVariable1 where
    asAst (ObjectSortVariable1 name) = SortVariableSort (SortVariable (Id name))
instance ObjectSort ObjectSortVariable1
