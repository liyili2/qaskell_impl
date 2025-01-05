{-# LANGUAGE BangPatterns #-}

module H.EnQ.ExactCover where

import Data.List (group, sort, maximumBy)
import Data.Ord (comparing)
import System.Random (randomRIO)
import Numeric.LinearAlgebra (Matrix, Vector, ident, cmap, fromLists, toList, flatten, (!), (<>), (#>), scale, expm, konst)
import Control.Monad (replicateM)

-- Generate Random Clauses
-- generateRandomClauses :: Int -> Int -> IO [[Int]]
-- generateRandomClauses _ _ = return [[0, 1, 2], [1, 2, 3]]

generateRandomClauses :: Int -> Int -> IO [[Int]]
generateRandomClauses n maxAttempts = go [] 0
  where
    go clauses attempts
      | attempts >= maxAttempts = error "Failed to generate a unique satisfying assignment instance."
      | otherwise = do
          clause <- fmap (take 3 . sort) $ replicateM 3 (randomRIO (0, n - 1))
          if clause `elem` clauses
            then go clauses (attempts + 1)
            else do
              let numSatisfying = countSatisfyingAssignments (clause : clauses) n
              if numSatisfying == 1
                then return (clause : clauses)
                else if numSatisfying == 0
                  then go clauses attempts
                  else go (clause : clauses) attempts

countSatisfyingAssignments :: [[Int]] -> Int -> Int
countSatisfyingAssignments clauses n =
  length [bits | bits <- generateChoices n, all (isValidClause bits) clauses]
  where
    isValidClause bits clause = sum (map (bits !!) clause) == 1

-- Problem Hamiltonian
problemHamiltonian :: [[Int]] -> Int -> Matrix Double
problemHamiltonian clauses n =
  fromLists [[if i == j then cost i else 0 | j <- [0 .. 2^n - 1]] | i <- [0 .. 2^n - 1]]
  where
    cost state =
      let bits = toBits n state
       in sum [1 | clause <- clauses, sum (map (bits !!) clause) /= 1]

-- Initial Hamiltonian
initialHamiltonian :: Int -> Matrix Double
initialHamiltonian n =
  fromLists [[if i /= j then -1 else 0 | j <- [0 .. 2^n - 1]] | i <- [0 .. 2^n - 1]]

-- Adiabatic Evolution
adiabaticEvolution :: Matrix Double -> Matrix Double -> Double -> Int -> Int -> Vector Double
adiabaticEvolution h0 hp t n steps =
  foldl evolve initialPsi [0 .. steps - 1]
  where
    dt = t / fromIntegral steps
    initialPsi = scale (1 / sqrt (fromIntegral (2^n))) (ident (2^n) #> onesVector)
    onesVector = konst 1 (2^n)
    evolve psi step =
      let time = fromIntegral step * dt
          ht = scale (1 - time / t) h0 + scale (time / t) hp
          ut = expm (scale (-dt) ht)
       in ut #> psi

toBits :: Int -> Int -> [Int]
toBits n x = reverse [if (x `div` 2^i) `mod` 2 == 1 then 1 else 0 | i <- [0 .. n - 1]]

randomSelect :: [Double] -> IO Int
randomSelect probs = do
  r <- randomRIO (0, sum probs)
  return $ selectIndex probs r 0
  where
    selectIndex (p : ps) r acc
      | r <= acc + p = 0
      | otherwise = 1 + selectIndex ps r (acc + p)
    selectIndex [] _ _ = error "Empty probabilities list"

-- Step 1: Generate Choices
generateChoices :: Int -> [[Int]]
generateChoices n = replicateM n [0, 1]

-- Step 2: Solve Classical
solveClassical :: [[Int]] -> ([Int] -> Bool)
solveClassical clauses =
  \bits -> all (isValidClause bits) clauses
  where
    isValidClause bits clause = sum (map (bits !!) clause) == 1

-- Step 3: Minimize Results
minimize :: ([Int] -> Bool) -> [[Int]] -> [[Int]]
minimize isValidChoice = filter isValidChoice

maxIndex :: Vector Double -> Int
maxIndex psi =
  fst $ maximumBy (comparing snd) (zip [0 ..] (map abs (toList psi)))

-- Main Example Usage
solveExactCover :: IO ()
solveExactCover = do
  let n = 4
  clauses <- generateRandomClauses n 1000
  putStrLn $ "Generated clauses: " ++ show clauses

  let t = 100.0
  let steps = 100
  let h0 = initialHamiltonian n
  let hp = problemHamiltonian clauses n
  let psiFinal = adiabaticEvolution h0 hp t n steps

  let index = maxIndex psiFinal
  let solution = toBits n index
  putStrLn $ "Quantum solution: " ++ show solution

  let classicalSolutions = minimize (solveClassical clauses) . generateChoices $ n
  putStrLn $ "Classical brute-force solutions: " ++ show classicalSolutions
