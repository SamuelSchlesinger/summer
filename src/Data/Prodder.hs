{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ConstraintKinds #-}
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
  , Consume(consume, extend1, cmap, produceB)
  , produce
  , empty
  , FoldProd(foldProd)
  , toList
  , type ForAll
  , atType
    -- ** Efficient Iterative Construction
  , buildProd
  , ProdBuilder
  , consB
  , emptyB
  , appendB
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
  , Strengthen(strengthenP)
  , strengthen
    -- * Transforming extensible products
  , remap
    -- * Picking out individual components of a product
  , Selection(select)
  , type FieldsFromSelector
  , type Selector
  ) where

import Data.ForAll (type ForAll)
import Control.Monad (unless)
import Control.Exception (catch, SomeException)
import GHC.Exts (Any, Constraint)
import Unsafe.Coerce (unsafeCoerce)
import Data.Functor.Identity (Identity (..))
import Data.Functor.Const (Const (..))
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import GHC.TypeLits (KnownNat, type (+), type (-), natVal, type (<=), Nat)
import Data.Proxy (Proxy(Proxy))
import Control.Monad.ST
import Data.STRef (newSTRef, STRef, writeSTRef, readSTRef)
import Data.Typeable (Typeable)
import Data.Monoid (Endo (Endo, appEndo))
import Data.List (intersperse)
import Data.Foldable (fold)

-- | An extensible product type
newtype Prod (xs :: [*]) = UnsafeProd { unProd :: Vector Any }
  deriving (Typeable)

-- | Showing extensible products.
instance FoldProd Show xs => Show (Prod xs) where
  showsPrec d xs = showParen (d > 10) . appEndo . fold $
    [Endo $ \r -> "[" <> r] <> intersperse (Endo $ \r -> ", " <> r) (toList @Show (Endo . showsPrec (d + 1)) xs) <> [Endo $ \r -> "]" <> r]

-- | Lens to modify one element of a product.
atType :: forall a b xs f. (a `HasIndexIn` xs, Functor f) => (a -> f b) -> Prod xs -> f (Prod (Replace a b xs))
atType f (UnsafeProd v) = fmap (\b -> UnsafeProd $ v V.// [(fromIntegral i, unsafeCoerce b)]) (f (unsafeCoerce (v V.! fromIntegral i))) where
  i = index @a @xs
{-# INLINE CONLIKE atType #-}

-- | A type for constructing products with linear memory use.
newtype ProdBuilder (xs :: [*]) = UnsafeProdBuilder { unProdBuilder :: forall s. STRef s Int -> V.MVector s Any -> ST s () }

-- | Cons an element onto the head of a 'ProdBuilder'.
consB :: x -> ProdBuilder xs -> ProdBuilder (x ': xs)
consB x (UnsafeProdBuilder b) = UnsafeProdBuilder \ref v -> withIncrement ref \i -> do
  MV.write v i (unsafeCoerce x)
{-# INLINE CONLIKE consB #-}

-- | Empty 'ProdBuilder'.
emptyB :: ProdBuilder '[]
emptyB = UnsafeProdBuilder \_ _ -> pure ()
{-# INLINE CONLIKE emptyB #-}

-- | Execute a 'ProdBuilder', pulling out a 'Prod'.
buildProd :: forall xs. (KnownNat (Length xs)) => ProdBuilder xs -> Prod xs
buildProd (UnsafeProdBuilder bs) = UnsafeProd $ V.create do
  ref <- newSTRef 0
  x <- MV.new (fromInteger $ natVal (Proxy @(Length xs)))
  bs ref x
  pure x
{-# INLINE CONLIKE buildProd #-}

-- | Appends two 'ProdBuilder's.
appendB :: ProdBuilder xs -> ProdBuilder ys -> ProdBuilder (xs <> ys)
appendB (UnsafeProdBuilder b) (UnsafeProdBuilder b') = UnsafeProdBuilder \ref v -> do
  b ref v
  b' ref v
{-# INLINE CONLIKE appendB #-}

-- | Creates a 'ProdBuilder' with a single element.
singletonB :: x -> ProdBuilder '[x]
singletonB x = consB x emptyB

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
extract = getConst . atType @x @() @xs Const
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
{-# INLINE CONLIKE dropFirst #-}

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
  Replace x y '[] = '[]

-- | Replaces one type with another via a function
remap :: forall x y xs. x `HasIndexIn` xs => (x -> y) -> Prod xs -> Prod (Replace x y xs)
remap f = runIdentity . atType @x @y @xs (Identity . f)
{-# INLINE CONLIKE remap #-}

-- | This is a reified pattern match on an extensible product
type family Consumer xs r where
  Consumer '[] r = r
  Consumer (x ': xs) r = x -> Consumer xs r

-- | A typeclass that is useful to define the scott encoding/decoding for
-- extensible products.
class Consume xs where
  consume :: forall r. Prod xs -> Consumer xs r -> r
  produceB :: (forall r. Consumer xs r -> r) -> ProdBuilder xs
  extend1 :: x -> Consumer xs (ProdBuilder (x ': xs))
  cmap :: (r -> r') -> Consumer xs r -> Consumer xs r' 

produce :: (KnownNat (Length xs), Consume xs) => (forall r. Consumer xs r -> r) -> Prod xs
produce f = buildProd $ produceB f
{-# INLINE CONLIKE produce #-}

empty :: Prod '[]
empty = buildProd $ produceB id
{-# INLINE CONLIKE empty #-}

instance Consume '[] where
  consume = flip const
  {-# INLINE CONLIKE consume #-}
  produceB x = emptyB
  {-# INLINE CONLIKE produceB #-}
  extend1 x = consB x emptyB
  {-# INLINE CONLIKE extend1 #-}
  cmap f x = f x
  {-# INLINE CONLIKE cmap #-}

withIncrement :: STRef s Int -> (Int -> ST s x) -> ST s x
withIncrement ref f = do
  i <- readSTRef ref
  x <- f i
  writeSTRef ref (i + 1)
  pure x
{-# INLINE CONLIKE withIncrement #-}

instance Consume xs => Consume (x ': xs) where
  consume (UnsafeProd v) g = consume @xs (UnsafeProd (V.tail v)) $ g (unsafeCoerce $ v V.! 0)
  {-# INLINE CONLIKE consume #-}
  produceB g = g (extend1 @xs)
  {-# INLINE CONLIKE produceB #-}
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
  strengthenP :: Prod xs -> ProdBuilder ys
strengthen :: (KnownNat (Length ys), Strengthen xs ys) => Prod xs -> Prod ys
strengthen = buildProd . strengthenP
{-# INLINE CONLIKE strengthen #-}
instance (Strengthen xs ys, y `HasIndexIn` xs) => Strengthen xs (y ': ys) where
  strengthenP p = consB (extract @y p) (strengthenP p)
  {-# INLINE CONLIKE strengthenP #-}
instance Strengthen xs '[] where
  strengthenP p = emptyB
  {-# INLINE CONLIKE strengthenP #-}

-- | A typeclass for creating a selection function which is valid on the given definition.
type family Selector def fields a where
  Selector def (field ': fields) a = Index field def -> Selector def fields a
  Selector def '[] a = a

-- | Extracts the fields intended from the given selector type.
type family FieldsFromSelector def selector where
  FieldsFromSelector def (a -> b) = IndexIn a def ': FieldsFromSelector def b
  FieldsFromSelector def (Identity a) = '[]

-- | A class for constructing the select function inductively.
class Selection def selector a where
  select :: Prod def -> selector -> a

instance Selection def a a where
  select _prod s = s
  {-# INLINE CONLIKE select #-}

instance (HasIndexIn x def, Selection def xs a) => Selection def (x -> xs) a where
  select prod f = select @_ @_ @a prod (f (extract @x prod))
  {-# INLINE CONLIKE select #-}

-- | A class for folding over a 'Prod' using a function which only requires that
-- every element of the product satisfy a certain constraint.
class ForAll c xs => FoldProd c xs where
  foldProd :: Monoid m => (forall a. c a => a -> m) -> Prod xs -> m

instance FoldProd c '[] where
  foldProd _f _p = mempty
  {-# INLINE CONLIKE foldProd #-}

instance (c x, FoldProd c xs) => FoldProd c (x ': xs) where
  foldProd f p = f x <> foldProd @c f (dropFirst p) where
    x = extract @x p
  {-# INLINE CONLIKE foldProd #-}

toList :: forall c xs a. FoldProd c xs => (forall x. c x => x -> a) -> Prod xs -> [a]
toList f = foldProd @c (pure . f)
{-# INLINE CONLIKE toList #-}
