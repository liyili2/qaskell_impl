{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module DSL.Tensor
  where

import Data.List

import Prettyprinter

import DSL.Utils
import DSL.Super.Simulated

newtype Tensor a = Tensor [a]
  deriving (Show, Functor, Applicative)

tensorPrecedence :: Int
tensorPrecedence = 2

instance Nesting a => Pretty (Tensor a) where
  pretty (Tensor []) = pretty "[]"
  pretty (Tensor xs) =
    hsep $ intersperse (pretty "⊗") $ map (prettyNested tensorPrecedence) xs

instance Nesting a => Nesting (Tensor a) where
  prettyNested p = parensWhen (p < tensorPrecedence) . pretty

