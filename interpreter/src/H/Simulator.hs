{-# LANGUAGE RankNTypes #-}

module H.Simulator
  ( Simulator(..)
  , classical
  , quantum
  , suggestT
  ) where

import Data.Bits (shiftL, testBit)
import Data.Complex (Complex(..), magnitude, cis, realPart)
import Data.List (minimumBy)
import Data.Ord (comparing)
import Data.Set (fromList, toAscList)
import System.Random (randomRIO)
import Control.Monad (replicateM)

-- Define the Simulator type
data Simulator = Simulator
  { n :: Int -- Number of spins
  , h :: [Int] -> Double -- Hamiltonian function
  }

-- Function to generate all spin configurations
generateSpins :: Int -> [[Int]]
generateSpins numSpins = map toSpins [0 .. (1 `shiftL` numSpins) - 1 :: Int]
  where
    toSpins :: Int -> [Int]
    toSpins config = [if testBit config i then 1 else -1 | i <- [0 .. numSpins - 1]]

-- Classical simulation function
classical :: Simulator -> ([Int], Double)
classical (Simulator numSpins hamiltonian) =
  let spinConfigs = generateSpins numSpins
      energies = [(spins, hamiltonian spins) | spins <- spinConfigs]
  in minimumBy (comparing snd) energies

-- Define the Hamiltonian matrix as a diagonal matrix
hamiltonianMatrix :: Simulator -> Int -> [Complex Double]
hamiltonianMatrix (Simulator numSpins hamiltonian) numStates =
  [realToFrac (hamiltonian spins) :+ 0 | spins <- generateSpins numSpins]
  where
    spinsForConfig config = [if testBit config i then 1 else -1 | i <- [0 .. numSpins - 1]]
    generateSpins n = map spinsForConfig [0 .. numStates - 1]

-- Time evolution operator
timeEvolution :: [Complex Double] -> Double -> [Complex Double]
timeEvolution hMatrix t = [cis (-energy * t) | energy <- map realPart hMatrix]

-- Interpolate between the initial and final Hamiltonians
interpolateHamiltonian :: [Complex Double] -> [Complex Double] -> Double -> [Complex Double]
interpolateHamiltonian hInitial hFinal s =
  zipWith (\hi hf -> ((1 :+ 0) - (s :+ 0)) * hi + (s :+ 0) * hf) hInitial hFinal

-- Evolve the state vector
evolveState :: [Complex Double] -> [Complex Double] -> [Complex Double]
evolveState u state = zipWith (*) u state

-- Quantum simulation function with time evolution
quantum :: Simulator -> Double -> Int -> Int -> IO ([Int], Double)
quantum sim totalTime shots numSteps = do
  let numStates = 2 ^ n sim
  let hFinal = hamiltonianMatrix sim numStates
  
  -- Construct initial Hamiltonian (transverse field)
  let hInitial = replicate numStates 0.0 ++ repeat ((-1.0) :+ 0.0)
  
  -- Initial state: equal superposition
  let initialState = replicate numStates (1 / sqrt (fromIntegral numStates) :+ 0)
  
  -- Time step for evolution
  let dt = totalTime / fromIntegral numSteps

  -- Perform adiabatic evolution
  let evolveStep state t = 
        let s = t / totalTime
            hT = interpolateHamiltonian hInitial hFinal s
            u = timeEvolution hT dt
        in evolveState u state
  
  -- Iterate over time steps
  let evolvedState = foldl evolveStep initialState [dt, 2*dt .. totalTime]
  
  -- Compute probabilities of outcomes
  let probabilities = map (\c -> magnitude c ** 2) evolvedState
  outcomes <- replicateM shots $ weightedChoice probabilities
  let counts = frequency outcomes
  
  -- Calculate energies for each observed state
  let energies = [(config, h sim (toSpins config)) | config <- map fst counts]
  let (bestConfig, bestEnergy) = minimumBy (comparing snd) energies
  return (toSpins bestConfig, bestEnergy)
  where
    toSpins config = [if testBit config i then 1 else -1 | i <- [0 .. n sim - 1]]

-- Helper function to sample outcomes based on probabilities
weightedChoice :: [Double] -> IO Int
weightedChoice weights = do
  let cumulative = scanl1 (+) weights
  let total = last cumulative
  r <- randomRIO (0, total)
  return $ length (takeWhile (< r) cumulative)

-- Helper function to compute frequency of outcomes
frequency :: [Int] -> [(Int, Int)]
frequency xs = [(x, length (filter (== x) xs)) | x <- unique xs]
  where
    unique = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- Compute all possible eigenvalues of the Hamiltonian
computeEigenvalues :: Int -> ([Int] -> Double) -> [Double]
computeEigenvalues numSpins hamiltonian =
  let spinConfigs = generateSpins numSpins
      eigenvalues = fromList [hamiltonian spins | spins <- spinConfigs]
  in toAscList eigenvalues

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
