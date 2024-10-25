module Main (main) where

import Lib
import Eval

import Data.Complex

import Test.QuickCheck

main :: IO ()
main = pure ()

genComplex :: Gen (Complex Double)
genComplex = liftA2 (:+) genDouble genDouble

genTensor :: Gen (TensorPower Basic)
genTensor = do
  n <- choose (2, 6)
  replicateM n genDouble

prop_equalSum :: Property
prop_equalSum = do
  tensor <- genTensor
  undefined

