{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Building.AsAst where

class AsAst a b where
    asAst :: b -> a
