module Clique where

import Eval2

-- Define a function to calculate clique energy based on edges in the graph.
-- It penalizes non-clique configurations by checking adjacency.
cliqueEnergy :: Graph Int -> Graph (Int, Int) -> Int -> Int
cliqueEnergy graph chosenEdges k =
    let numNodes = length (vertices graph)
        -- Sum adjacency values where edges form part of the clique
        numEdges = foldr (\(_, adj) acc -> acc + adj) 0 chosenEdges
    in (k - numNodes) ^ 2 + ((k * (k - 1) `div` 2) - numEdges) ^ 2

-- Find cliques by minimizing energy.
findClique :: Graph Int -> Int -> [Graph (Int, Int)] -> [(Graph (Int, Int), Int)]
findClique graph k candidates = 
    [(candidate, cliqueEnergy graph candidate k) | candidate <- candidates]

-- Example usage: find cliques in `exampleGraph` with k = 3.
testClique :: IO ()
testClique = do
    -- Define exampleGraph with cliques and non-clique connections
    let exampleGraph = Graph 
            { vertices = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
            , edges = [ (1, 1, 2), (2, 1, 3), (1, 1, 3)  -- Clique 1: Nodes 1, 2, 3
                      , (4, 1, 5), (5, 1, 6), (4, 1, 6)  -- Clique 2: Nodes 4, 5, 6
                      , (7, 1, 8), (8, 1, 9), (9, 1, 10), (7, 1, 9), (7, 1, 10), (8, 1, 10)  -- Clique 3: Nodes 7, 8, 9, 10
                      , (3, 1, 4)  -- Connect Clique 1 to Clique 2
                      , (2, 1, 7)  -- Connect Clique 1 to Clique 3
                      , (6, 1, 8)  -- Connect Clique 2 to Clique 3
                      , (11, 1, 12)  -- Isolated edge, not part of any clique
                      , (13, 1, 14), (13, 1, 15)  -- Small non-clique group: Nodes 13, 14, 15
                      ]
            }
    let choices = generateChoices 1 (-1) exampleGraph
    let results = findClique exampleGraph 3 choices
    print results
