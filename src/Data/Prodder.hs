{-# LANGUAGE BlockArguments #-}
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
  , Consume(consume, extend1, cmap)
  , produce
    -- * Type families
  , Index
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
import qualified Data.Vector.Mutable as MV
import GHC.TypeLits (KnownNat, type (+), type (-), natVal, type (<=), Nat)
import Data.Proxy (Proxy(Proxy))
import Control.Monad.ST
import Data.STRef (newSTRef, STRef, writeSTRef, readSTRef)

-- | An extensible product type
newtype Prod (xs :: [*]) = UnsafeProd { unProd :: Vector Any }

newtype ProdBuilder (xs :: [*]) = UnsafeProdBuilder { unProdBuilder :: forall s. STRef s Int -> V.MVector s Any -> ST s () }

buildProd :: forall xs. (KnownNat (Length xs)) => ProdBuilder xs -> Prod xs
buildProd (UnsafeProdBuilder bs) = UnsafeProd $ V.create do
  ref <- newSTRef 0
  x <- MV.new (fromInteger $ natVal (Proxy @(Length xs)))
  bs ref x
  pure x

type role Prod representational

-- | A type family for computing the index of a type in a list of types.
type family IndexIn (x :: k) (xs :: [k]) where
  IndexIn x (x ': xs) = 0
  IndexIn x (y ': xs) = 1 + IndexIn x xs

-- | A type family for indexing into lists of types.
type family Index (n :: Nat) (xs :: [k]) where
  Index 0 (x ': xs) = x
  Index n (_ ': xs) = Index (n - 1) xs

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
  produceBuilder :: (forall r. Consumer xs r -> r) -> ProdBuilder xs
  extend1 :: x -> Consumer xs (ProdBuilder (x ': xs))
  cmap :: (r -> r') -> Consumer xs r -> Consumer xs r' 

produce :: (KnownNat (Length xs), Consume xs) => (forall r. Consumer xs r -> r) -> Prod xs
produce f = buildProd $ produceBuilder f

instance Consume '[] where
  consume = flip const
  {-# INLINE CONLIKE consume #-}
  produceBuilder x = UnsafeProdBuilder \ref v -> pure ()
  {-# INLINE CONLIKE produceBuilder #-}
  extend1 x = UnsafeProdBuilder \ref v -> withIncrement ref \i -> MV.write v i (unsafeCoerce x)
  {-# INLINE CONLIKE extend1 #-}
  cmap f x = f x
  {-# INLINE CONLIKE cmap #-}

withIncrement :: STRef s Int -> (Int -> ST s x) -> ST s x
withIncrement ref f = do
  i <- readSTRef ref
  x <- f i
  writeSTRef ref (i + 1)
  pure x

instance Consume xs => Consume (x ': xs) where
  consume (UnsafeProd v) g = consume @xs (UnsafeProd (V.tail v)) $ g (unsafeCoerce $ v V.! 0)
  {-# INLINE CONLIKE consume #-}
  produceBuilder g = g (extend1 @xs)
  {-# INLINE CONLIKE produceBuilder #-}
  cmap f = fmap (cmap @xs f)
  {-# INLINE CONLIKE cmap #-}
  extend1 (x1 :: x1) x = cmap @xs @(ProdBuilder (x ': xs)) @(ProdBuilder (x1 ': x ': xs)) f (extend1 @xs x) where
    f (UnsafeProdBuilder b) = UnsafeProdBuilder \ref v -> (withIncrement ref \i -> MV.write v i (unsafeCoerce x1)) >> b ref v
    
      
     
  -- cmap @xs @(Prod (x ': xs)) @(Prod (x1 ': x ': xs)) (UnsafeProd . (V.singleton (unsafeCoerce x1) V.++) . unProd) (extend1 @xs x)
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
