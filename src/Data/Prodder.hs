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
{- |
Module: Data.Prodder
Copyright: (c) Samuel Schlesinger 2020
License: MIT
Maintainer: sgschlesinger@gmail.com
Stability: experimental
Portability: non-portable
Description: Extensible products
-}
module Data.Prodder
  ( -- * The extensible product type
    Prod
    -- * Construction and deconstruction
  , extract
  , index
  , tailN
  , initN
  , dropFirst
  , Consume(consume, produce, extend1, cmap)
    -- * Type families
  , IndexIn
  , HasIndexIn
  , Consumer
  , type (<>)
  , Length
  , Tail
  , Init
  , Replace
    -- * Rearranging and removing elements
  , Strengthen(strengthen)
    -- * Transforming extensible products
  , remap
  ) where

import Control.Monad (unless)
import Control.Exception (catch, SomeException)
import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.TypeLits (KnownNat, type (+), type (-), natVal, type (<=))
import Data.Proxy (Proxy(Proxy))

-- | An extensible product type
data Prod (xs :: [*]) = UnsafeProd { unProd :: Vector Any }

type role Prod representational

-- | A type family for computing the index of a type in a list of types.
type family IndexIn (x :: k) (xs :: [k]) where
  IndexIn x (x ': xs) = 0
  IndexIn x (y ': xs) = 1 + IndexIn x xs

-- | A type family for computing the length of a type level list
type family Length (xs :: [k]) where
  Length '[] = 0
  Length (x ': xs) = 1 + Length xs

-- | A type family for computing the tail of a type level list
type family Tail n xs where
  Tail 0 xs = xs
  Tail n (x ': xs) = Tail (n - 1) xs

-- | A type family for computing the initial segment of a type level list
type family Init n xs where
  Init 0 xs = '[]
  Init n (x ': xs) = x ': Init (n - 1) xs

-- | A class that is used for convenience in order to make certain type
-- signatures read more clearly.
class KnownNat (x `IndexIn` xs) => x `HasIndexIn` xs
instance KnownNat (x `IndexIn` xs) => x `HasIndexIn` xs

-- | Computes the index of the given type in the given type level list.
index :: forall x xs. x `HasIndexIn` xs => Word
index = fromInteger $ natVal (Proxy @(IndexIn x xs))
{-# INLINE CONLIKE index #-}

-- | Extract a value at a particular index
extract :: forall x xs. x `HasIndexIn` xs => Prod xs -> x
extract (UnsafeProd v) = unsafeCoerce $ v V.! fromIntegral (index @x @xs)
{-# INLINE CONLIKE extract #-}

-- | Takes the tail of a product after the nth element.
tailN :: forall n xs. (KnownNat n, n <= Length xs) => Prod xs -> Prod (Tail n xs)
tailN (UnsafeProd v) = UnsafeProd $ V.slice n (V.length v - n) v
  where
    n = fromInteger $ natVal (Proxy @n)
{-# INLINE CONLIKE tailN #-}

-- | Takes the initial length n segment of a product.
initN :: forall n xs. (KnownNat n, n <= Length xs) => Prod xs -> Prod (Init n xs)
initN (UnsafeProd v) = UnsafeProd $ V.slice 0 n v
  where
    n = fromInteger $ natVal (Proxy @n)
{-# INLINE CONLIKE initN #-}

-- | Drop the first element of a product. Sometimes needed for better type
-- inference and less piping around of constraints.
dropFirst :: forall x xs. Prod (x ': xs) -> Prod xs
dropFirst (UnsafeProd v) = UnsafeProd $ V.slice 1 (V.length v - 1) v


type family (<>) (xs :: [k]) (ys :: [k]) :: [k] where
  '[] <> ys = ys
  (x ': xs) <> ys = x ': (xs <> ys)
combine :: forall xs ys. Prod xs -> Prod ys -> Prod (xs <> ys)
combine (UnsafeProd p) (UnsafeProd q) = UnsafeProd (p V.++ q)
{-# INLINE CONLIKE combine #-}

-- | Type family for replacing one type in a type level list with another
type family Replace x y xs where
  Replace x y (x ': xs) = y ': xs
  Replace x y (z ': xs) = z ': Replace x y xs

-- | Replaces one type with another via a function
remap :: forall x y xs. x `HasIndexIn` xs => (x -> y) -> Prod xs -> Prod (Replace x y xs)
remap f (UnsafeProd v) = UnsafeProd (update `V.imap` v) where
  update :: Int -> Any -> Any
  update (fromIntegral -> n) a
    | n == index @x @xs = unsafeCoerce $ f $ unsafeCoerce a
    | otherwise = a
  {-# INLINE CONLIKE update #-}
{-# INLINE CONLIKE remap #-}

-- | This is a reified pattern match on an extensible product
type family Consumer xs r where
  Consumer '[] r = r
  Consumer (x ': xs) r = x -> Consumer xs r

-- | A typeclass that is useful to define the scott encoding/decoding for
-- extensible products.
class Consume xs where
  consume :: forall r. Prod xs -> Consumer xs r -> r
  produce :: (forall r. Consumer xs r -> r) -> Prod xs
  extend1 :: x -> Consumer xs (Prod (x ': xs))
  cmap :: (r -> r') -> Consumer xs r -> Consumer xs r' 

instance Consume '[] where
  consume = flip const
  {-# INLINE CONLIKE consume #-}
  produce x = UnsafeProd V.empty
  {-# INLINE CONLIKE produce #-}
  extend1 x = UnsafeProd (V.singleton (unsafeCoerce x))
  {-# INLINE CONLIKE extend1 #-}
  cmap f x = f x
  {-# INLINE CONLIKE cmap #-}

instance Consume xs => Consume (x ': xs) where
  consume (UnsafeProd v) g = consume @xs (UnsafeProd (V.tail v)) $ g (unsafeCoerce $ v V.! 0)
  {-# INLINE CONLIKE consume #-}
  produce g = g (extend1 @xs)
  {-# INLINE CONLIKE produce #-}
  cmap f = fmap (cmap @xs f)
  {-# INLINE CONLIKE cmap #-}
  extend1 (x1 :: x1) x = cmap @xs @(Prod (x ': xs)) @(Prod (x1 ': x ': xs)) (UnsafeProd . (V.singleton (unsafeCoerce x1) V.++) . unProd) (extend1 @xs x)
  {-# INLINE CONLIKE extend1 #-}

instance Eq (Prod '[]) where
  _ == _ = True
  {-# INLINE CONLIKE (==) #-}

instance (Eq x, Eq (Prod xs)) => Eq (Prod (x ': xs)) where
  px@(UnsafeProd x) == py@(UnsafeProd y) = unsafeCoerce @_ @x (x V.! 0) == unsafeCoerce @_ @x (y V.! 0) && dropFirst px == dropFirst py
  {-# INLINE CONLIKE (==) #-}

-- | A typeclass to rearrange and possibly remove things from a product.
class Strengthen xs ys where
  strengthen :: Prod xs -> Prod ys
instance (Strengthen xs ys, y `HasIndexIn` xs) => Strengthen xs (y ': ys) where
  strengthen p = UnsafeProd $ V.singleton (unsafeCoerce $ unProd p V.! fromIntegral (index @y @xs)) <> unProd (strengthen @xs @ys p)
  {-# INLINE CONLIKE strengthen #-}
instance Strengthen xs '[] where
  strengthen = const (UnsafeProd V.empty)
  {-# INLINE CONLIKE strengthen #-}
