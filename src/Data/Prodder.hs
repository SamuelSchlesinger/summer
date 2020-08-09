{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Prodder
  ( Prod
  , IndexIn
  , HasIndexIn
  , (<>)
  , extract
  , index
  , remap
  , dropFirst
  , Consumer
  , Consume(consume, produce, extend1, cmap)
  -- * TODO remove when making an actual package
  , prodTest
  ) where

import Control.Monad (unless)
import Control.Exception (catch, SomeException)
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.TypeLits (KnownNat, type (+), natVal)
import Data.Proxy (Proxy(Proxy))

data Prod (xs :: [*]) = UnsafeProd { unProd :: Vector Any }

type role Prod representational

type family IndexIn (x :: k) (xs :: [k]) where
  IndexIn x (x ': xs) = 0
  IndexIn x (y ': xs) = 1 + IndexIn x xs

class KnownNat (x `IndexIn` xs) => x `HasIndexIn` xs
instance KnownNat (x `IndexIn` xs) => x `HasIndexIn` xs

index :: forall x xs. x `HasIndexIn` xs => Word
index = fromInteger $ natVal (Proxy @(IndexIn x xs))

extract :: forall x xs. x `HasIndexIn` xs => Prod xs -> x
extract (UnsafeProd v) = unsafeCoerce $ v V.! fromIntegral (index @x @xs)

dropFirst :: forall x xs. Prod (x ': xs) -> Prod xs
dropFirst (UnsafeProd v) = UnsafeProd $ V.slice 1 (V.length v - 1) v

type family (<>) (xs :: [k]) (ys :: [k]) :: [k] where
  '[] <> ys = ys
  (x ': xs) <> ys = x ': (xs <> ys)
combine :: forall xs ys. Prod xs -> Prod ys -> Prod (xs <> ys)
combine (UnsafeProd p) (UnsafeProd q) = UnsafeProd (p V.++ q)

type family Replace x y xs where
  Replace x y (x ': xs) = y ': xs
  Replace x y (z ': xs) = z ': Replace x y xs

remap :: forall x y xs. x `HasIndexIn` xs => (x -> y) -> Prod xs -> Prod (Replace x y xs)
remap f (UnsafeProd v) = UnsafeProd (update `V.imap` v) where
  update :: Int -> Any -> Any
  update (fromIntegral -> n) a
    | n == index @x @xs = unsafeCoerce $ f $ unsafeCoerce a
    | otherwise = a

-- TODO: Implement co-weakening

type family Consumer xs r where
  Consumer '[] r = r
  Consumer (x ': xs) r = x -> Consumer xs r

class Consume xs where
  consume :: forall r. Prod xs -> Consumer xs r -> r
  produce :: (forall r. Consumer xs r -> r) -> Prod xs
  extend1 :: x -> Consumer xs (Prod (x ': xs))
  cmap :: (r -> r') -> Consumer xs r -> Consumer xs r' 

instance Consume '[] where
  consume = flip const
  produce x = UnsafeProd V.empty
  extend1 x = UnsafeProd (V.singleton (unsafeCoerce x))
  cmap f x = f x

instance Consume xs => Consume (x ': xs) where
  consume (UnsafeProd v) g = consume @xs (UnsafeProd (V.tail v)) $ g (unsafeCoerce $ v V.! 0)
  produce g = g (extend1 @xs)
  cmap f = fmap (cmap @xs f)
  extend1 (x1 :: x1) x = cmap @xs @(Prod (x ': xs)) @(Prod (x1 ': x ': xs)) (UnsafeProd . (V.singleton (unsafeCoerce x1) V.++) . unProd) (extend1 @xs x)

instance Eq (Prod '[]) where
  _ == _ = True

instance (Eq x, Eq (Prod xs)) => Eq (Prod (x ': xs)) where
  px@(UnsafeProd x) == py@(UnsafeProd y) = unsafeCoerce @_ @x (x V.! 0) == unsafeCoerce @_ @x (y V.! 0) && dropFirst px == dropFirst py

class Strengthen xs ys where
  strengthen :: Prod xs -> Prod ys
instance (Strengthen xs ys, y `HasIndexIn` xs) => Strengthen xs (y ': ys) where
  strengthen p = UnsafeProd $ V.singleton (unsafeCoerce $ unProd p V.! fromIntegral (index @y @xs)) <> unProd (strengthen @xs @ys p)
instance Strengthen xs '[] where
  strengthen = const (UnsafeProd V.empty)

prodTest :: IO ()
prodTest = catchAndDisplay
  [ indexTest
  , remapTest
  , consumeAndProduceTest
  , extractTest
  , strengthenTest
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
