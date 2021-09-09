{-# LANGUAGE BlockArguments #-}
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

require :: Bool -> String -> IO ()
require p s = unless p $ fail s

requires' :: String -> [Bool] -> IO ()
requires' msg = mapM_ (\(i, b) -> require b (msg <> " " <> show i)) . zip [1..]

requires :: [(Bool, String)] -> IO ()
requires = mapM_ (uncurry require)

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
      requires' "index"
        [ index' == 1
        , index'' == 0
        ]
    remapTest = do
      let x :: Prod '[Int, Bool] = produce (\f -> f 10 True)
      let y = remap ((+ 10000000000000000000000000000) . toInteger @Int) x
      let z = remap not x
      requires' "remap"
        [ y == produce (\f -> f 10000000000000000000000000010 True)
        , z == produce (\f -> f 10 False)
        ]
    consumeAndProduceTest = do
      let x :: Prod '[Int, Bool] = produce (\f -> f 10 True)
          y :: Bool = consume x (\n b -> n == 10 && b)
      require y "Consuming and producing does not work"
    extractTest = do
      let x :: Prod '[Int, Bool] = produce (\f -> f 10 True)
          y :: Bool = extract x
          z :: Int = extract x
      require (z == 10 && y) "Extracting does not work"
    strengthenTest = do
      let x :: Prod '[Int, Bool, Float] = produce (\f -> f 10 True 0.1)
          y :: Prod '[Bool, Int, Float] = strengthen x
          z :: Prod '[Bool, Int] = strengthen x
      requires
        [ (y == produce (\f -> f True 10 0.1), "strengthen doesn't work 1")
        , (z == produce (\f -> f True 10), "strengthen doesn't work 2")
        ]
    initNTest = do
      let x :: Prod '[Int, Bool, Char, Float] = produce (\f -> f 10 True 'a' 0.2)
      requires
        [ (initN @0 x == produce id, "tailN does not work 0")
        , (initN @1 x == produce (\f -> f 10), "tailN does not work 1")
        , (initN @2 x == produce (\f -> f 10 True), "tailN does not work 2")
        , (initN @3 x == produce (\f -> f 10 True 'a'), "tailN does not work 3")
        , (initN @4 x == produce (\f -> f 10 True 'a' 0.2), "tailN does not work 4")
        ]
    tailNTest = do
      let x :: Prod '[Int, Bool, Char, Float] = produce (\f -> f 10 True 'a' 0.2)
      requires
        [ (tailN @0 x == x, "tailN does not work 0")
        , (tailN @1 x == produce (\f -> f True 'a' 0.2), "tailN does not work 1")
        , (tailN @2 x == produce (\f -> f 'a' 0.2), "tailN does not work 2")
        , (tailN @3 x == produce (\f -> f 0.2), "tailN does not work 3")
        , (tailN @4 x == produce id, "tailN does not work 3")
        ]
    selectTest = do
      let x :: Prod '[Int, Bool, Char, Float] = produce (\f -> f 10 True 'a' 0.2)
      requires
        [ (select x (\(n :: Int) -> n == 10), "select does not work 0")
        , (select x (\(f :: Float) -> f == 0.2), "select does not work 1")
        , (select x (\(b :: Bool) (f :: Float) -> b && f == 0.2), "select does not work 2")
        ]
    prodBuilderTest = do
      requires
        [ (empty == buildProd emptyB, "prodBuilder does not work 0")
        , (produce (\f -> f "Hello") == buildProd (consB "Hello" emptyB), "prodBuilder does not work 1")
        ]
    foldProdTest = do
      let x :: Prod '[String, Bool] = produce \f -> f "Hello" True
      requires
        [ (toList @Show show x == [show "Hello", show True], "toList does not work 0")
        , (toList @Eq (\a -> a == a) x == [True, True], "toList does not work 1")
        ]

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
      require (tag' == 1) ("Tag " <> show tag' <> " does not equal 1")
    eqTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Int, Bool] = Inj True
          z :: Sum '[Int, Bool] = Inj (11 :: Int)
          -- wrap around the alphabet like fromIntegral
          a :: Sum '[Int, Bool] = Inj (10 :: Int)
          b :: Sum '[Int, Bool] = Inj False
          c :: Sum '[Int, Bool] = Inj True
      requires
        [ (x /= y, "10 equals True")
        , (x /= z, "10 equals 11")
        , (x == a, "10 does not equal 10")
        , (y /= b, "True equals False")
        , (y == c, "True does not equal True")
        ]
    noOpWeakenTest = do
      let x :: Sum '[Int, Bool]  = Inj (10 :: Int)
          y :: Sum '[Int, Bool, Integer] = noOpWeaken x
      require (y == Inj (10 :: Int)) "y does not equal Inj 10"
      pure ()
    weakenTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Bool, Int] = weaken x
          z :: Sum '[Integer, Bool, Float, Int] = weaken y
      requires
        [ (y == Inj (10 :: Int), "y does not equal Inj 10")
        , (z == Inj (10 :: Int), "y does not equal Inj 10")
        ]
    matchTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
      require (match x (== 10) id) "x does not match 10"
    considerTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Int, Bool] = Inj True
      requires
        [ (consider @Int x == Right 10, "x at Int is not considered to be 10"),
          (consider @Int y == Left (Inj True), "x is not considered to be Left (Inj True)"),
          (consider @Bool y == Right True, "x at Bool is not considered to be Right True")
        ]
    inmapTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Int, Bool] = inmap (== (10 :: Int)) x
          z :: Sum '[Int, Bool] = inmap (== True) x
      requires
        [ (y == Inj True, "x did not get mapped to True")
        , (z == Inj (10 :: Int), "x did not get left alone")
        ]
    smapTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Bool, Int] = smap (== (10 :: Int)) x
          z :: Sum '[Bool, Int] = smap (== True) x
      requires
        [ (y == Inj True, "x did not get mapped to True")
        , (z == Inj (10 :: Int), "x did not get left alone")
        ]
    unmatchTest = do
      let x :: Sum '[Int, Bool] = Inj True
          y = \f g -> f 100
      require (x == unmatch (match x)) "match and unmatch are not an inverse pair"
    applyTest = do
      let x :: Sum '[Int, Bool] = Inj False
      require (apply @Show show x == "False") "apply does not work 0"
    unorderedMatchTest = do
      let x :: Sum '[Int, Bool] = Inj False
      require (unorderedMatch @_ @'[Bool, Int] x not (== 10)) "unordered match does not work 0"
