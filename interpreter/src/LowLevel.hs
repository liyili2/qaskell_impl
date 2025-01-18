{-# LANGUAGE GADTs #-}

module LowLevel
  where

import DSL.Super.Simulated
import Lib

import Control.Monad

keepZero :: Int -> TensorPower Bit -> Super ()
keepZero i bitVec = guard (tensorIndex bitVec i == zeroBit)

keepOne :: Int -> TensorPower Bit -> Super ()
keepOne i bitVec = guard (tensorIndex bitVec i == oneBit)

swap :: Int -> Int -> TensorPower Bit -> TensorPower Bit
swap i j bitVec@(TensorPower xs0) = TensorPower (go 0 xs0)
  where
    iBit = tensorIndex bitVec i
    jBit = tensorIndex bitVec j

    go _currIndex [] = []
    go currIndex (x:xs)
      | currIndex == i = jBit : go (currIndex+1) xs
      | currIndex == j = iBit : go (currIndex+1) xs
      | otherwise      = x    : go (currIndex+1) xs

