{-# LANGUAGE ScopedTypeVariables #-}

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

eqSum :: forall m. (Foldable m, MonadPlus m) =>
  Proxy m -> -- This is just so that the m is unambiguous, since it isn't used in the rest of the type
  [Int] ->
  Int
eqSum Proxy ns = solveF choices
  where
    choices :: m (Components [] Proxy Int)
    choices = fmap components listElementChoices

    listElementChoices :: m [IntWeighted Int]
    listElementChoices = generateChoices 1 (-1) ns

    components :: [IntWeighted Int] -> Components [] Proxy Int
    components weightedElems =
      Components
          -- hA
        (map (foldWeighted (*)) weightedElems)

          -- hB (stays 0)
        Proxy

graphPartition :: forall m. (Foldable m, MonadPlus m) =>
  Proxy m -> -- This is just so that the m is unambiguous, since it isn't used in the rest of the type
  AdjMatrix () ->
  Int
graphPartition Proxy adj = solveF choices
  where
    nodes :: [()]
    nodes = getNodes adj

    choices :: m (Components [] AdjMatrix Int)
    choices = fmap components nodeWeightChoices

    nodeWeightChoices :: m [IntWeighted ()]
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
    adjacencySumBody (Weighted w1 (), Weighted w2 ()) = (1 - (w1 * w2)) `div` 2

-- NOTE: For instance, you can run this at GHCi:
-- ghci> eqSum (Proxy @[]) list1

list1 :: [Int]
list1 = [1,3,4]

list2 :: [Int]
list2 = [2,3,4]


--  A --- B    D
--  |    /     |
--  |   /      |
--  |  /       |
--  | /        |
--  C          E
graph1 :: AdjMatrix ()
graph1 =
  adjMatrix
    [ -- A --
        -- A      B        C        D        E
      [Nothing, Just (), Just (), Nothing, Nothing]

      -- B --
        -- A      B        C        D        E
    , [Just (), Nothing, Just (), Nothing, Nothing]

      -- C --
        -- A      B        C        D        E
    , [Just (), Just (), Nothing, Nothing, Nothing]

      -- D --
        -- A      B        C        D        E
    , [Nothing, Nothing, Nothing, Nothing, Just ()]

      -- E --
        -- A      B        C        D        E
    , [Nothing, Nothing, Nothing, Just (), Nothing]
    ]

-- A --- B
-- |     |
-- |     |
-- C     D
graph2 :: AdjMatrix ()
graph2 =
  adjMatrix
    [ -- A
        -- A      B       C        D
      [Nothing, Just (), Just (), Nothing]

      -- B
        -- A      B       C        D
    , [Just (), Nothing, Nothing, Just ()]

      -- C
        -- A      B       C        D
    , [Just (), Nothing, Nothing, Nothing]

      -- D
    , [Nothing, Just (), Nothing, Nothing]
    ]

