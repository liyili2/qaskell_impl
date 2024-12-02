-- Simulated (quantum) superpositions
-- 
-- Idea: If we only access this through the interface exposed by the module, then
-- we should be able to compile to an actual quantum program.
--
-- Based on the probability monad from Tikhon Jelvis' talk here: https://www.youtube.com/watch?v=qZ4O-1VYv4c
-- That talk, in turn, is based on
--  - Probabilistic Functional Programming in Haskell by Martin Erwig and Steve Kollmansberger
--  - Practical Probabilistic Programming with Monads by Adam Scibior, Zoubin Ghahramani and Andrew D. Gordon

{-# LANGUAGE TupleSections #-}

module DSL.Super.Simulated
    (Super
    ,Prob
    ,uniform
    ,choice
    ,send
    )
  where

import Data.Complex
import Data.Bifunctor

import Control.Monad
import Control.Applicative

import qualified Data.Random as R
import qualified Data.Random.Distribution.Categorical as R
import qualified System.Random.MWC as R

import Data.Ratio

newtype SuperP p a = Super [(p, a)]
  deriving (Functor)

instance Num p => Applicative (SuperP p) where
  pure x = Super [(1, x)]
  (<*>) = ap

instance Num p => Monad (SuperP p) where
  m >>= f = join' (fmap f m)
    where
      join' :: SuperP p (SuperP p a) -> SuperP p a
      join' (Super ds) =
        Super
          [ (p1 * p2, x)
            | (p1, Super d) <- ds
            , (p2, x) <- d
          ]

instance Num p => Alternative (SuperP p) where
  empty = Super []
  Super xs <|> Super ys = Super (xs ++ ys) -- TODO: Is this correct?

instance Num p => Foldable (SuperP p) where
  foldMap f (Super xs) =
    -- TODO: Is this correct?
    foldMap (f . snd) xs

instance Num p => MonadPlus (SuperP p)

type Prob = Rational

type Super = SuperP Prob
-- type SuperC = SuperP (Complex Int)

uniform :: [a] -> Super a
uniform xs = Super (zip (repeat 1) xs)

choice :: [(Prob, a)] -> Super a
choice = Super

-- TODO: Do we need this?
combineDuplicates :: (Num p, Eq a) => SuperP p a -> SuperP p a
combineDuplicates (Super xs) =
  Super (foldr (uncurry addTo) [] xs)

addTo :: (Num p, Eq a) => p -> a -> [(p, a)] -> [(p, a)]
addTo p0 v = go p0
  where
    go p [] = [(p, v)]
    go p ((p', v'):xs)
      | v' == v = go (p + p') xs
      | otherwise = (p', v') : go p xs

normalize :: Super a -> Super a
normalize (Super xs) =
  let probs = map fst xs
      probSum = sum probs
  in
  Super (map (first (/ probSum)) xs)

send :: Eq a => Super a -> IO a
send s = do
  mwc <- R.create
  let Super xs = normalize (combineDuplicates s)
  R.sampleFrom mwc (R.categorical (map (first (fromRational @Double)) xs))

