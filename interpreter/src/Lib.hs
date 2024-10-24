{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lib
  where

import Control.Applicative

import Data.Complex

-- TODO: Probability amplitudes
newtype Choice a = Choice [a]
  deriving (Show, Semigroup, Monoid, Functor, Applicative, Monad, Alternative)

newtype TensorPower a = TensorPower [a]
  deriving (Show, Semigroup, Monoid, Functor)

choice :: [a] -> Choice a
choice = Choice

zipWithChoices :: (a -> b -> c) -> Choice a -> Choice b -> Choice c
zipWithChoices f (Choice xs) (Choice ys) = Choice (zipWith f xs ys)

runChoice :: Choice a -> [a]
runChoice (Choice xs) = xs

-- cartesianProduct :: [Tensor a] -> [Tensor a]
-- cartesianProduct = undefined

type Basic = Complex Double

type Env = Choice (TensorPower Basic)

tensorIndex :: TensorPower a -> Int -> a
tensorIndex (TensorPower xs) j = xs !! j

singletonTensor :: a -> TensorPower a
singletonTensor x = TensorPower [x]

