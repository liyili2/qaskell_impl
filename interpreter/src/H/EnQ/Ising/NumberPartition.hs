module H.EnQ.Ising.NumberPartition
    ( numberPartitionH
    , testNumberPartitionH
    ) where

import H.EnQ.Ising.Ising (generateSpins, solveHamiltonians, findMinimum, solveClassical, solveQuantum, suggestT)

-- Define the Hamiltonian for the number partitioning problem
numberPartitionH :: [Int] -> [Int] -> Double
numberPartitionH numbers spins =
  let weightedSum = sum $ zipWith (*) numbers spins
  in fromIntegral (weightedSum ^ 2)

testNumberPartitionH :: IO ()
testNumberPartitionH = do
  let numbers = [3, 1, 4, 2, 2]
  let numSpins = length numbers
  let hamiltonian spins = numberPartitionH numbers spins
  let shots = 1024
  let numSteps = 100

  -- Suggest optimal t based on energy gap
  let onError err = error ("Error in suggestT: " ++ err)
  let onSuccess optimalT = optimalT
  let optimalT = suggestT numSpins hamiltonian onError onSuccess
  putStrLn $ "Suggested optimal t: " ++ show optimalT

  -- Generate spin configurations
  let spins = generateSpins numSpins

  -- Run classical simulation
  putStrLn "Running classical simulation..."
  classicalResults <- solveHamiltonians (solveClassical hamiltonian) numSpins
  let classicalMin = findMinimum classicalResults
  putStrLn $ "Classical Result: Configuration: " ++ show (snd classicalMin) ++ ", Energy: " ++ show (fst classicalMin)

  -- Run quantum simulation
  putStrLn "Running quantum simulation..."
  quantumResults <- solveHamiltonians (\spins -> solveQuantum hamiltonian optimalT shots spins numSteps) numSpins
  let quantumMin = findMinimum quantumResults
  putStrLn $ "Quantum Result: Configuration: " ++ show (snd quantumMin) ++ ", Energy: " ++ show (fst quantumMin)
