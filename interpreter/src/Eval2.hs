module Eval2 where

import Control.Monad

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

-- Some small example trees for experimentation

tr1, tr2, tr3 :: Tree Int
tr1 = Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)
tr2 = Node (Leaf 10) (Node (Leaf 20) (Leaf 30))
tr3 = Node tr1 (Node tr1 tr2)

------------------------------------------------------------------------------
-- We want to create choices at each position in a data structure
-- and from that, create a choice of data structures.

-- This is the basic abstraction of "traverse". We will traverse the
-- data structure with a MonadPlus operation representing (weighted) choices.
-- For now we use integers to represent the weights.

generateChoices :: (MonadPlus m, Traversable t) => 
                   Int -> Int -> t a -> m (t (Int,a))
generateChoices d1 d2 = traverse $ \a -> return (d1 , a) `mplus` return (d2 , a)

-- Now that we generated all the choices we need to fold over the choices
-- to choose the "minimum" one or more generally the one(s) satisfying
-- the desired constraints

energy :: Foldable t => t (Int,Int) -> Int
energy ch = sq $ foldr (\(d,a) s -> s + d*a) 0 ch
  where sq a = a * a

solveF :: (Functor f, Foldable f, Foldable t) => f (t (Int,Int)) -> Int
solveF chs = foldr1 min $ fmap energy chs

-- The equal sum example

eqSumL :: [Int] -> Int
eqSumL ns = solveF choices
  where choices :: [[(Int,Int)]]
        choices = generateChoices 1 (-1) ns

{--

ghci> eqSumL [10,20,30]
0
ghci> eqSumL [1,5,2,8,10]
0
ghci> eqSumL [1,5,7,8,10]
1

--}

-- A version of equal sum for trees

eqSumT :: Tree Int -> Int
eqSumT tr = solveF choices
  where choices :: [ Tree (Int,Int) ]
        choices = generateChoices 1 (-1) tr

{--

ghci> eqSumT tr2
0

--}

------------------------------------------------------------------------------
