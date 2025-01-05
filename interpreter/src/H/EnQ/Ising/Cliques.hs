module H.EnQ.Ising.Cliques
    ( cliquesH
    , testCliquesH
    ) where

import H.EnQ.Ising.Ising (generateSpins, solveHamiltonians, findMinimum, solveClassical, solveQuantum, suggestT)

-- Define the Hamiltonian for the clique problem
cliquesH :: [(Int, Int)] -> Int -> [Int] -> Double
cliquesH edges k spins =
  let -- First term: Enforce clique size
      term1 = fromIntegral $ (k - sum spins) ^ 2

      -- Second term: Enforce clique completeness
      term2 = fromIntegral $ (k * (k - 1)) `div` 2 - sum [spins !! u * spins !! v | (u, v) <- edges]

      -- Weights for terms
      a, b :: Double
      a = 1.0
      b = 1.0
  in a * term1 + b * term2

-- Test the clique Hamiltonian with FunctionalSimulator
testCliquesH :: IO ()
testCliquesH = do
  let edges = [(0, 1), (1, 2), (2, 3), (3, 0), (0, 2)] -- Example graph (square with a diagonal)
  let numVertices = 4
  let k = 3 -- Desired clique size
  let hamiltonian spins = cliquesH edges k spins
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
