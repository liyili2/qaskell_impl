{-# LANGUAGE GADTs #-}

module DSL.LowLevel
  where

import Prettyprinter

import DSL.Utils

data Operator a where
  Keep1 :: a -> Operator a -- | Keep1 x   <--->   a*(x) ∘ a(x)
  Keep0 :: a -> Operator a -- | Keep0 x   <--->   a(x) ∘ a*(x)
  deriving (Show)

instance Pretty a => Pretty (Operator a) where
  pretty (Keep1 x) = pretty "Keep1" <> parens (pretty x)
  pretty (Keep0 x) = pretty "Keep2" <> parens (pretty x)

data Expr where
  Lit :: Int -> Expr
  deriving (Show)

instance Pretty Expr where pretty = pretty . show

-- Tensor (Super (Operator Expr)) -> Super (Tensor (Operator Expr))

