module H.EnQ.Ising.GraphPartition
    ( graphPartitionH
    , testGraphPartitionH
    ) where

import H.EnQ.Ising.Ising (generateSpins, solveHamiltonians, findMinimum, solveClassical, solveQuantum, suggestT)

-- Define the Hamiltonian for the graph partitioning problem
graphPartitionH :: [(Int, Int)] -> [Int] -> Double
graphPartitionH edges spins =
  let -- First term: size constraint
      term1 = fromIntegral $ sum spins ^ 2
      -- Second term: edge penalty
      term2 = sum [ (1 - fromIntegral (spins !! u * spins !! v)) / 2 | (u, v) <- edges ]
      -- Weights for terms
      a = 1.0
      b = 1.0
  in a * term1 + b * term2

testGraphPartitionH :: IO ()
testGraphPartitionH = do
  let edges = [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)] -- Example graph (a square with a diagonal)
  let numVertices = 4
  let hamiltonian spins = graphPartitionH edges spins
  let shots = 1024
  let numSteps = 100

  -- Suggest optimal t based on energy gap
  let onError err = error ("Error in suggestT: " ++ err)
  let onSuccess optimalT = optimalT
  let optimalT = suggestT numVertices hamiltonian onError onSuccess
  putStrLn $ "Suggested optimal t: " ++ show optimalT

  -- Generate spin configurations
  let spins = generateSpins numVertices

  -- Run classical simulation
  putStrLn "Running classical simulation..."
  classicalResults <- solveHamiltonians (solveClassical hamiltonian) numVertices
  let classicalMin = findMinimum classicalResults
  putStrLn $ "Classical Result: Configuration: " ++ show (snd classicalMin) ++ ", Energy: " ++ show (fst classicalMin)

  -- Run quantum simulation
  putStrLn "Running quantum simulation..."
  quantumResults <- solveHamiltonians (\spins -> solveQuantum hamiltonian optimalT shots spins numSteps) numVertices
  let quantumMin = findMinimum quantumResults
  putStrLn $ "Quantum Result: Configuration: " ++ show (snd quantumMin) ++ ", Energy: " ++ show (fst quantumMin)
