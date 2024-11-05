module Eval3 where

import Control.Monad

import Data.Proxy

import AdjMatrix

------------------------------------------------------------------------------
-- We are given some traversable data structure. Basic examples include
-- the list type [a] from the Haskell library and trees as defined below

data Tree a = Leaf a | Node (Tree a) (Tree a)
  deriving Show

instance Functor Tree where
  fmap f (Leaf a) = Leaf (f a) 
  fmap f (Node t1 t2) = Node (fmap f t1) (fmap f t2)

instance Foldable Tree where
  foldr f b (Leaf a) = f a b
  foldr f b (Node t1 t2) = foldr f (foldr f b t2) t1

instance Traversable Tree where
  traverse f (Leaf a) = pure Leaf <*> f a
  traverse f (Node t1 t2) = pure Node <*> traverse f t1 <*> traverse f t2

data Weighted a b =
  Weighted
    { wWeight :: a
    , wValue :: b
    }
  deriving (Functor, Show)

foldWeighted :: (a -> b -> r) -> Weighted a b -> r
foldWeighted f (Weighted w v) = f w v

type IntWeighted = Weighted Int

------------------------------------------------------------------------------
-- We want to create choices at each position in a data structure
-- and from that, create a choice of data structures.

-- This is the basic abstraction of "traverse". We will traverse the
-- data structure with a MonadPlus operation representing (weighted) choices.
-- For now we use integers to represent the weights.

generateChoices :: (MonadPlus m, Traversable t) => 
                   Int -> Int -> t a -> m (t (IntWeighted a))
generateChoices d1 d2 struct =
    traverse (\a -> return (Weighted d1 a) `mplus` return (Weighted d2 a))
             struct

data Components s t a =
  Components
    { cHA :: s a
    , cHB :: t a
    }
  deriving (Functor, Show)

-- Now that we generated all the choices we need to fold over the choices
-- to choose the "minimum" one or more generally the one(s) satisfying
-- the desired constraints

sqrtEnergy :: Foldable t => t (Int,Int) -> Int
sqrtEnergy ch = foldr (\(d,a) s -> s + d*a) 0 ch
  -- where sq a = a * a

energy :: Foldable t => t (Int,Int) -> Int
energy = sq . sqrtEnergy
  where
    sq a = a * a

-- TODO: Generalize to things that don't square the hA
sumComponents :: (Foldable s, Foldable t) => Components s t Int -> Int
sumComponents comp =
  sq (sum (cHA comp)) + sum (cHB comp)
  where
    sq a = a * a

solveF :: (Functor f, Foldable f, Foldable s, Foldable t) =>
  f (Components s t Int) -> Int
solveF chs = foldr1 min $ fmap sumComponents chs

type Choices = []

-- () values are just placeholders. The node's location in the list tells
-- you where its value appears in the adjacency matrix.
nodeWeights :: [()] -> Choices [IntWeighted ()]
nodeWeights = generateChoices 1 (-1)

listWeights :: [a] -> Choices [IntWeighted a]
listWeights = generateChoices 1 (-1)

---- Examples ----

eqSum :: [Int] -> Int
eqSum ns = solveF choices
  where
    choices :: Choices (Components [] Proxy Int)
    choices = map components listElementChoices

    listElementChoices :: Choices [IntWeighted Int]
    listElementChoices = generateChoices 1 (-1) ns

    components :: [IntWeighted Int] -> Components [] Proxy Int
    components weightedElems =
      Components
          -- hA
        (map (foldWeighted (*)) weightedElems)

          -- hB (stays 0)
        Proxy

graphPartition :: [()] -> AdjMatrix ((), ()) -> Int
graphPartition nodes adj = solveF choices
  where
    choices :: Choices (Components [] AdjMatrix Int)
    choices = map components nodeWeightChoices

    nodeWeightChoices :: Choices [IntWeighted ()]
    nodeWeightChoices = generateChoices 1 (-1) nodes

    components :: [IntWeighted ()] -> Components [] AdjMatrix Int
    components nodeWeights =
      let adj' :: AdjMatrix (IntWeighted (), IntWeighted ())
          adj' = updateNodeContents adj nodeWeights
      in
      Components
          -- hA
        (fmap (foldWeighted (\x () -> x)) nodeWeights)
        
          -- hB
        (fmap adjacencySumBody adj')

    adjacencySumBody :: (IntWeighted (), IntWeighted ()) -> Int
    adjacencySumBody (Weighted w1 (), Weighted w2 ()) = w1 * w2

