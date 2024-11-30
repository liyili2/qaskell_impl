{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module DSL.MinSpanTree
  (findMinimalTree, computeH, generateTrees) where

import DSL.AdjMatrix (AdjMatrix, getEdges, getNodes)
import DSL.Solve (generateChoices, Weighted(..), unWeighted, solveF)
import Control.Monad (MonadPlus, msum)
import Data.Proxy (Proxy(..))
import Data.List (subsequences)

type Node = Int
type Edge = (Node, Node)

-- Compute H_A and H_B for a specific tree and root
computeH :: [Edge] -> AdjMatrix a -> Int -> Int -> Node -> Double -> Double -> Double
computeH tree adjMatrix n maxDegree root a b = hA + hB
  where
    -- BFS to determine depths
    depths = bfsDepths tree root

    -- Calculate degrees for each node
    degrees = foldl (\acc (u, v) -> incrementDegree u (incrementDegree v acc)) [] tree

    -- Unique depth term: count unvisited nodes (depth = maxBound)
    uniqueDepth = a * fromIntegral (length [() | (_, d) <- depths, d == maxBound])

    -- Degree constraint: penalty for exceeding max degree
    degreeConstraint = a * fromIntegral (sum [max 0 (deg - maxDegree) | (_, deg) <- degrees])

    -- Connectivity term: penalize if not all nodes are reachable
    connectivity = a * fromIntegral ((n - length depths) ^ 2)

    -- H_A and H_B terms
    hA = uniqueDepth + degreeConstraint + connectivity
    hB = b * fromIntegral (length tree)

-- Increment the degree of a node in the list
incrementDegree :: Node -> [(Node, Int)] -> [(Node, Int)]
incrementDegree node [] = [(node, 1)]
incrementDegree node ((n, d):rest)
    | n == node = (n, d + 1) : rest
    | otherwise = (n, d) : incrementDegree node rest

-- Perform BFS to calculate depths from a given root
bfsDepths :: [Edge] -> Node -> [(Node, Int)]
bfsDepths tree root = go [(root, 0)] [root]
  where
    edgeMap = buildAdjList tree
    go [] visited = [(v, maxBound) | v <- concatMap (\(u, v) -> [u, v]) tree, v `notElem` visited]
    go ((current, depth):queue) visited =
        let neighbors = filter (`notElem` visited) (lookupDefault current edgeMap [])
            visited' = visited ++ neighbors
            depths' = [(n, depth + 1) | n <- neighbors]
        in (current, depth) : go (queue ++ depths') visited'

-- Build adjacency list from edges
buildAdjList :: [Edge] -> [(Node, [Node])]
buildAdjList edges = foldl addEdge [] edges
  where
    addEdge acc (u, v) = addNeighbor u v (addNeighbor v u acc)
    addNeighbor u v [] = [(u, [v])]
    addNeighbor u v ((x, ns):rest)
        | x == u = (x, v : ns) : rest
        | otherwise = (x, ns) : addNeighbor u v rest

-- Lookup with a default value
lookupDefault :: Eq a => a -> [(a, b)] -> b -> b
lookupDefault key [] def = def
lookupDefault key ((k, v):rest) def
    | key == k = v
    | otherwise = lookupDefault key rest def

subsetStrategy :: (MonadPlus m, Traversable t) => [b] -> t a -> m (t (Weighted b a))
subsetStrategy weights struct =
  traverse (\a -> msum (map (\w -> return (Weighted w a)) weights)) struct
  
-- Generate trees with weighted edges and compute H for each configuration
generateTrees :: (MonadPlus m, Eq a) => Double -> Double -> Int -> AdjMatrix a -> m Double
generateTrees a b maxDegree adjMatrix = do
    let edges = getEdges adjMatrix
    let n = length (getNodes adjMatrix)

    -- Use subset strategy to generate weighted edges
    weightedEdges <- generateChoices (subsetStrategy [1, 0]) edges

    -- Extract the chosen edges from the weighted structure
    let chosenEdges = map unWeighted weightedEdges

    -- Allow any node to be the root
    root <- msum (map return [0 .. n - 1])

    -- Compute the energy for the current spanning tree and root
    let h = computeH chosenEdges adjMatrix n maxDegree root a b

    return h

-- Main function to find the minimal spanning tree
findMinimalTree :: forall m. (Foldable m, MonadPlus m) =>
  Proxy m -> Int -> AdjMatrix () -> Double
findMinimalTree Proxy maxDegree adjMatrix =
    solveF (generateTrees 10 1 maxDegree adjMatrix :: m Double)
