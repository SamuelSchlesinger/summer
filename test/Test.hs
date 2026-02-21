{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Control.Exception
import Control.Monad
import Data.Functor.Identity (Identity(..))
import Data.Summer
import Data.Prodder
import qualified Generics.SOP as SOP

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
  , prodBuilderTest
  , selectTest
  , foldProdTest
  , showTest
  , dropFirstTest
  , appendBTest
  , atTypeTest
  , emptyEqTest
  , extractMiddleTest
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
    showTest = do
      let x :: Prod '[Int, Bool, Char, Float] = produce (\f -> f 10 True 'a' 0.2)
      require (show x == "[10, True, 'a', 0.2]") "show product 0"
    dropFirstTest = do
      let x :: Prod '[Int, Bool, Char] = produce (\f -> f 10 True 'a')
          y :: Prod '[Bool, Char] = dropFirst x
      requires' "dropFirst"
        [ extract @Bool y == True
        , extract @Char y == 'a'
        ]
    appendBTest = do
      let ab = consB (1 :: Int) (consB True emptyB)
          cd = consB 'x' (consB (2.0 :: Float) emptyB)
          combined :: Prod '[Int, Bool, Char, Float] = buildProd (appendB ab cd)
      requires' "appendB"
        [ extract @Int combined == 1
        , extract @Bool combined == True
        , extract @Char combined == 'x'
        , extract @Float combined == 2.0
        ]
    atTypeTest = do
      let x :: Prod '[Int, Bool, Char] = produce (\f -> f 10 True 'a')
          y :: Prod '[Int, Bool, Char] = runIdentity $ atType @Bool @Bool (\b -> Identity (not b)) x
          z :: Prod '[Int, Bool, Char] = runIdentity $ atType @Int @Int (\n -> Identity (n + 100)) x
      requires' "atType"
        [ extract @Bool y == False
        , extract @Int y == 10
        , extract @Char y == 'a'
        , extract @Int z == 110
        , extract @Bool z == True
        ]
    emptyEqTest = do
      let x :: Prod '[] = empty
          y :: Prod '[] = empty
      require (x == y) "empty products are not equal"
    extractMiddleTest = do
      let x :: Prod '[Char, Bool, Int, Float] = produce (\f -> f 'z' False 42 3.14)
      requires' "extract middle"
        [ extract @Char x == 'z'
        , extract @Bool x == False
        , extract @Int x == 42
        , extract @Float x == 3.14
        ]

sumTest :: IO ()
sumTest = catchAndDisplay
  [ tagTest
  , eqTest
  , noOpWeakenTest
  , weakenTest
  , matchTest
  , considerTest
  , considerFirstTest
  , inspectTest
  , inmapTest
  , smapTest
  , unmatchTest
  , applyTest
  , unorderedMatchTest
  , showTest
  , matchMultiVariantTest
  , weakenNonFirstTest
  , genericsSopTest
  , variantTest
  , threeVariantConsiderTest
  , unmatchRoundtripAllPositionsTest
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
          z :: Sum '[Int, Bool, Char] = Inj @Int 10
      requires' "consider"
        [ consider @Int x == Right 10
        , consider @Int y == Left (Inj True)
        , consider @Bool y == Right True
        , consider @Bool z == Left (Inj @Int 10)
        ]
    considerFirstTest = do
      let x :: Sum '[Int, Bool] = Inj (10 :: Int)
          y :: Sum '[Int, Bool] = Inj True
      requires' "considerFirst"
        [ considerFirst x == Right (10 :: Int)
        , considerFirst y == Left (Inj True)
        ]
    inspectTest = do
      let x :: Sum '[Int, Bool, Char] = Inj (42 :: Int)
      requires' "inspect"
        [ inspect @Int x == Just 42
        , inspect @Bool x == Nothing
        , inspect @Char x == Nothing
        , inspect @Bool (Inj True :: Sum '[Int, Bool]) == Just True
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
      requires' "unordered match"
        [ unorderedMatch x not (\(x :: Int) -> x == 10)
        , unorderedMatch x (\(x :: Int) -> x == 10) not
        ]
    showTest = do
      let x :: Sum '[Int, Bool] = Inj False
      let y :: Sum '[Int, Bool] = Inj @Int 1
      requires' "show sum"
        [ show x == "Inj @Bool (False)"
        , show y == "Inj @Int (1)"
        ]
    matchMultiVariantTest = do
      let x :: Sum '[Int, Bool, Char] = Inj 'z'
          y :: Sum '[Int, Bool, Char] = Inj True
          z :: Sum '[Int, Bool, Char] = Inj (99 :: Int)
      requires' "match multi-variant"
        [ match x (const 'a') (const 'b') id == 'z'
        , match y (const 'a') (\b -> if b then 'T' else 'F') id == 'T'
        , match z (\n -> if n == 99 then 'Y' else 'N') (const 'b') id == 'Y'
        ]
    weakenNonFirstTest = do
      let x :: Sum '[Int, Bool] = Inj True
          y :: Sum '[Bool, Int] = weaken x
          z :: Sum '[Char, Bool, Int] = weaken x
      requires' "weaken non-first variant"
        [ y == Inj True
        , z == Inj True
        , inspect @Bool y == Just True
        , inspect @Bool z == Just True
        ]
    genericsSopTest = do
      let x :: Sum '[Int, Bool] = Inj (42 :: Int)
          y :: Sum '[Int, Bool] = Inj True
          roundtrip :: Sum '[Int, Bool] -> Sum '[Int, Bool]
          roundtrip = SOP.to . SOP.from
      requires' "generics-sop"
        [ roundtrip x == x
        , roundtrip y == y
        ]
    variantTest = do
      let x :: Sum '[Int, Bool, Char] = Inj (10 :: Int)
          y :: Sum '[Int, Bool, Char] = Inj True
      requires' "variant prism"
        [ runIdentity (variant @Int @Int (\n -> Identity (n * 2)) x) == Inj (20 :: Int)
        , runIdentity (variant @Int @Int (\n -> Identity (n * 2)) y) == Inj True
        , inspect @Int (runIdentity (variant @Int @Int (\n -> Identity (n + 5)) x)) == Just 15
        ]
    threeVariantConsiderTest = do
      let x :: Sum '[Int, Bool, Char] = Inj 'a'
      requires' "three variant consider"
        [ consider @Int x == Left (Inj 'a' :: Sum '[Bool, Char])
        , consider @Bool x == Left (Inj 'a' :: Sum '[Int, Char])
        , consider @Char x == Right 'a'
        ]
    unmatchRoundtripAllPositionsTest = do
      let x :: Sum '[Int, Bool, Char] = Inj (7 :: Int)
          y :: Sum '[Int, Bool, Char] = Inj False
          z :: Sum '[Int, Bool, Char] = Inj 'q'
      requires' "unmatch roundtrip all positions"
        [ unmatch (match x) == x
        , unmatch (match y) == y
        , unmatch (match z) == z
        ]
      
