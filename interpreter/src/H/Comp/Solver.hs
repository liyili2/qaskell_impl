module H.Fn.Solver
    ( generateSpins
    , solveHamiltonians
    , findMinimum
    , solveClassical
    , solveQuantum
    , testSolver
    , suggestT
    ) where

import Data.Bits (shiftL, testBit)
import Data.Complex (Complex(..), magnitude, cis, realPart)
import Data.List (minimumBy)
import Data.Ord (comparing)
import Control.Monad (replicateM)
import System.Random (randomRIO)
import qualified Data.Set as Set  -- Import Data.Set

-- Generate all spin configurations
generateSpins :: Int -> [[Int]]
generateSpins numSpins = map toSpins ([0 .. (1 `shiftL` numSpins) - 1] :: [Int])
  where
    toSpins :: Int -> [Int]
    toSpins config = [if testBit config i then 1 else -1 | i <- [0 .. numSpins - 1]]

-- Solve the Hamiltonians using a solver function (classical or quantum)
solveHamiltonians :: ([[Int]] -> IO [(Double, [Int])]) -> Int -> IO [(Double, [Int])]
solveHamiltonians solver numSpins = solver (generateSpins numSpins)

-- Find the configuration with the minimum energy
findMinimum :: [(Double, [Int])] -> (Double, [Int])
findMinimum = minimumBy (comparing fst)

-- Classical solver
solveClassical :: ([Int] -> Double) -> [[Int]] -> IO [(Double, [Int])]
solveClassical hamiltonian spins = do
    let energies = [(hamiltonian s, s) | s <- spins]
    return energies

-- Quantum solver with time evolution
solveQuantum :: ([Int] -> Double) -> Double -> Int -> [[Int]] -> Int -> IO [(Double, [Int])]
solveQuantum hamiltonian totalTime shots spins numSteps = do
    let numStates = length spins

    -- Initial Hamiltonian (H_B): Transverse field
    let hInitial = replicate numStates (0.0 :+ 0.0) ++ repeat ((-1.0) :+ 0.0)

    -- Problem Hamiltonian (H_P): From the given Hamiltonian function
    let hFinal = map (\s -> hamiltonian s :+ 0) spins

    -- Initial state: Equal superposition
    let initialState = replicate numStates (1 / sqrt (fromIntegral numStates) :+ 0)

    -- Time step for evolution
    let dt = totalTime / fromIntegral numSteps

    -- Time evolution using small steps
    let evolveStep state t =
            let s = t / totalTime
                hT = zipWith (\hi hf -> ((1 :+ 0) - (s :+ 0)) * hi + (s :+ 0) * hf) hInitial hFinal
                u = [cis (-realPart energy * dt) | energy <- hT]
            in zipWith (*) u state

    -- Perform evolution over time steps
    let evolvedState = foldl evolveStep initialState [0, dt .. totalTime]

    -- Compute probabilities of outcomes
    let probabilities = map (\c -> magnitude c ** 2) evolvedState
    outcomes <- replicateM shots $ weightedChoice probabilities
    let counts = frequency outcomes

    -- Calculate energies for each observed state
    return [(hamiltonian (spins !! config), spins !! config) | (config, _) <- counts]

-- Weighted choice for quantum sampling
weightedChoice :: [Double] -> IO Int
weightedChoice weights = do
    let cumulative = scanl1 (+) weights
    let total = last cumulative
    r <- randomRIO (0, total)
    return $ length (takeWhile (< r) cumulative)

-- Frequency helper function
frequency :: [Int] -> [(Int, Int)]
frequency xs = [(x, length (filter (== x) xs)) | x <- unique xs]
  where
    unique = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- Compute all possible eigenvalues of the Hamiltonian
computeEigenvalues :: Int -> ([Int] -> Double) -> [Double]
computeEigenvalues numSpins hamiltonian =
  let spinConfigs = generateSpins numSpins
      eigenvalues = Set.fromList [hamiltonian spins | spins <- spinConfigs]
  in Set.toAscList eigenvalues

-- Suggest an optimal time t based on the energy gap
suggestT :: Int -> ([Int] -> Double) -> (String -> Double) -> (Double -> Double) -> Double
suggestT numSpins hamiltonian onError onSuccess =
  let eigenvalues = computeEigenvalues numSpins hamiltonian
  in if length eigenvalues < 2
       then onError "Insufficient eigenvalues to compute energy gap."
       else
         let gaps = zipWith (-) (tail eigenvalues) eigenvalues
             deltaE = minimum gaps
         in if deltaE == 0
              then onError "Zero energy gap detected."
              else onSuccess (1 / deltaE)

testSolver :: IO ()
testSolver = do
    let numSpins = 4
    let hamiltonian spins = fromIntegral (sum spins ^ 2)  -- Example Hamiltonian
    let t = 1.0
    let shots = 1024
    let numSteps = 100

    -- Run classical simulation
    let spins = generateSpins numSpins
    classicalResults <- solveHamiltonians (solveClassical hamiltonian) numSpins
    let classicalMin = findMinimum classicalResults
    putStrLn $ "Classical Minimum: " ++ show classicalMin

    -- Suggest optimal time `t` based on the energy gap
    let onError err = error ("Error in suggestT: " ++ err)
    let onSuccess optimalT = optimalT
    let optimalT = suggestT numSpins hamiltonian onError onSuccess
    putStrLn $ "Suggested optimal t: " ++ show optimalT

    -- Run quantum simulation
    putStrLn "Running quantum simulation..."
    quantumResults <- solveHamiltonians (\spins -> solveQuantum hamiltonian optimalT shots spins numSteps) numSpins
    let quantumMin = findMinimum quantumResults
    putStrLn $ "Quantum Minimum: Configuration: " ++ show (snd quantumMin) ++ ", Energy: " ++ show (fst quantumMin)
