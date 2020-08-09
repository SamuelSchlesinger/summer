{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Control.Exception
import Control.Monad
import Data.Summer
import Data.Prodder

main :: IO ()
main = sumTest >> prodTest

prodTest :: IO ()
prodTest = catchAndDisplay
  [ indexTest
  , remapTest
  , consumeAndProduceTest
  , extractTest
  , strengthenTest
  , tailNTest
  , initNTest
  ]
  where
    catchAndDisplay (x : xs) = catch @SomeException x print >> catchAndDisplay xs
    catchAndDisplay [] = pure ()
    indexTest = do
      let index' = index @Int @'[Bool, Int]
          index'' = index @Bool @'[Bool, Int]
      unless (index' == 1) $ fail ("Index " <> show index' <> " does not equal 1")
      unless (index'' == 0) $ fail ("Index " <> show index'' <> " does not equal 0")
    remapTest = do
      let x :: Prod '[Int, Bool] = produce (\f -> f 10 True)
      let y = remap ((+ 10000000000000000000000000000) . toInteger @Int) x
      let z = remap not x
      unless (y == produce (\f -> f 10000000000000000000000000010 True)) $ fail "Remapping does not work 1"
      unless (z == produce (\f -> f 10 False)) $ fail "Remapping does not work 2"
    consumeAndProduceTest = do
      let x :: Prod '[Int, Bool] = produce (\f -> f 10 True)
          y :: Bool = consume x (\n b -> n == 10 && b)
      unless y $ fail "Consuming and producing does not work"
    extractTest = do
      let x :: Prod '[Int, Bool] = produce (\f -> f 10 True)
          y :: Bool = extract x
          z :: Int = extract x
      unless (z == 10 && y) $ fail "Extracting does not work"
    strengthenTest = do
      let x :: Prod '[Int, Bool, Float] = produce (\f -> f 10 True 0.1)
          y :: Prod '[Bool, Int, Float] = strengthen x
          z :: Prod '[Bool, Int] = strengthen x
      unless (y == produce (\f -> f True 10 0.1)) $ fail "strengthen doesn't work 1"
      unless (z == produce (\f -> f True 10)) $ fail "strengthen doesn't work 2"
    initNTest = do
      let x :: Prod '[Int, Bool, Char, Float] = produce (\f -> f 10 True 'a' 0.2)
      unless (initN @0 x == produce id) $ fail "tailN does not work 0"
      unless (initN @1 x == produce (\f -> f 10)) $ fail "tailN does not work 1"
      unless (initN @2 x == produce (\f -> f 10 True)) $ fail "tailN does not work 2"
      unless (initN @3 x == produce (\f -> f 10 True 'a')) $ fail "tailN does not work 3"
      unless (initN @4 x == produce (\f -> f 10 True 'a' 0.2)) $ fail "tailN does not work 4"
    tailNTest = do
      let x :: Prod '[Int, Bool, Char, Float] = produce (\f -> f 10 True 'a' 0.2)
      unless (tailN @0 x == x) $ fail "tailN does not work 0"
      unless (tailN @1 x == produce (\f -> f True 'a' 0.2)) $ fail "tailN does not work 1"
      unless (tailN @2 x == produce (\f -> f 'a' 0.2)) $ fail "tailN does not work 2"
      unless (tailN @3 x == produce (\f -> f 0.2)) $ fail "tailN does not work 3"
      unless (tailN @4 x == produce id) $ fail "tailN does not work 3"

sumTest :: IO ()
sumTest = catchAndDisplay
  [ tagTest
  , eqTest
  , noOpWeakenTest
  , weakenTest
  , matchTest
  , considerTest
  , inmapTest
  , smapTest
  , unmatchTest
  ]
  where
    catchAndDisplay (x : xs) = catch @SomeException x print >> catchAndDisplay xs
    catchAndDisplay [] = pure ()
    tagTest = do
      let tag' = tag @Int @'[Bool, Int]
          tag'' = tag @Bool @'[Bool, Int]
      unless (tag' == 1) $ fail ("Tag " <> show tag' <> " does not equal 1")
    eqTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Int, Bool] = Inj True
          z :: Sum '[Int, Bool] = Inj (11 :: Int)
          -- wrap around the alphabet like fromIntegral
          a :: Sum '[Int, Bool] = Inj (10 :: Int)
          b :: Sum '[Int, Bool] = Inj False
          c :: Sum '[Int, Bool] = Inj True
      unless (x /= y) $ fail "10 equals True"
      unless (x /= z) $ fail "10 equals 11"
      unless (x == a) $ fail "10 does not equal 10"
      unless (y /= b) $ fail "True equals False"
      unless (y == c) $ fail "True does not equal True"
    noOpWeakenTest = do
      let x :: Sum '[Int, Bool]  = Inj (10 :: Int)
          y :: Sum '[Int, Bool, Integer] = noOpWeaken x
      unless (y == Inj (10 :: Int)) $ fail "y does not equal Inj 10"
      pure ()
    weakenTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Bool, Int] = weaken x
          z :: Sum '[Integer, Bool, Float, Int] = weaken y
      unless (y == Inj (10 :: Int)) $ fail "y does not equal Inj 10"
      unless (z == Inj (10 :: Int)) $ fail "y does not equal Inj 10"
    matchTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
      unless (match x (== 10) id) $ fail "x does not match 10"
    considerTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Int, Bool] = Inj True
      unless (consider @Int x == Right 10) $ fail "x at Int is not considered to be 10"
      unless (consider @Int y == Left (Inj True)) $ fail $ "x is not considered to be Left (Inj True)"
      unless (consider @Bool y == Right True) $ fail "x at Bool is not considered to be Right True"
    inmapTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Int, Bool] = inmap (== (10 :: Int)) x
          z :: Sum '[Int, Bool] = inmap (== True) x
      unless (y == Inj True) $ fail "x did not get mapped to True"
      unless (z == Inj (10 :: Int)) $ fail "x did not get left alone"
    smapTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Bool, Int] = smap (== (10 :: Int)) x
          z :: Sum '[Bool, Int] = smap (== True) x
      unless (y == Inj True) $ fail "x did not get mapped to True"
      unless (z == Inj (10 :: Int)) $ fail "x did not get left alone"
    unmatchTest = do
      let x :: Sum '[Int, Bool] = Inj True
          y = \f g -> f 100
      unless (x == unmatch (match x)) $ fail "match and unmatch are not an inverse pair"
