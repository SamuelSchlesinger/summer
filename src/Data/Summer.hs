{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE DataKinds #-}
{- |
Module: Data.Summer
Copyright: (c) Samuel Schlesinger 2020
License: MIT
Maintainer: sgschlesinger@gmail.com
Stability: experimental
Portability: non-portable
Description: Extensible sums
-}
module Data.Summer
  ( -- * The extensible sum type and its associated pattern for convenience
    Sum
  , pattern Inj
  -- * Construction and Deconstruction
  , inject
  , inspect
  , consider
  , Match(match, override, unmatch)
  -- * Type families
  , TagIn
  , HasTagIn
  , Delete
  , HaveSameTagsIn
  , Matcher
  -- * Weakening extensible sums
  , Weaken(weaken)
  , noOpWeaken
  -- * Transforming extensible sums
  , inmap
  , smap
  -- * Tests TODO Remove when making a real package
  , sumTest
  ) where

import Control.Exception (catch, SomeException)
import Unsafe.Coerce (unsafeCoerce)
import GHC.Exts (Any, Constraint)
import GHC.TypeLits (Nat, KnownNat, natVal, type (+))
import Data.Proxy (Proxy(Proxy))
import Data.Kind (Type)
import Control.Monad (unless)

-- | The extensible sum type, allowing inhabitants to be of any of the
-- types in the given type list.
data Sum (xs :: [*]) = UnsafeInj {-# UNPACK #-} !Word Any

type role Sum representational

-- | A pattern to match on for convenience. Without this, the user facing
-- interface is rather baroque.
pattern Inj :: forall x xs. (x `HasTagIn` xs) => x -> Sum xs
pattern Inj x <- (inspect -> Just x)
  where
    Inj x = inject x

-- | A type family for computing the tag of a given type in an extensible
-- sum. In practice, this means computing the first index of the given type in
-- the list.
type family TagIn (x :: k) (xs :: [k]) where
  TagIn x (x ': xs) = 0
  TagIn x (y ': xs) = 1 + TagIn x xs

-- | A class that is used for convenience in order to make certain
-- type signatures read more clearly.
class KnownNat (x `TagIn` xs) => x `HasTagIn` xs
instance KnownNat (x `TagIn` xs) => x `HasTagIn` xs

-- | Computes the tag of the given type in the given type level list.
tag :: forall x xs. x `HasTagIn` xs => Word
tag = fromInteger $ natVal (Proxy @(TagIn x xs))
{-# INLINE CONLIKE tag #-}

-- | Injects a type into the extensible sum.
inject :: forall x xs. (x `HasTagIn` xs) => x -> Sum xs
inject x = UnsafeInj (tag @x @xs) (unsafeCoerce x)
{-# INLINE CONLIKE inject #-}

-- | Inspects an extensible sum for a particular type.
inspect :: forall x xs. (x `HasTagIn` xs) => Sum xs -> Maybe x
inspect (UnsafeInj tag' x) = if tag @x @xs == tag' then Just (unsafeCoerce x) else Nothing
{-# INLINE CONLIKE inspect #-}

-- | A type family for deleting the given type from a list
type family Delete (x :: k) (xs :: [k]) :: [k] where
  Delete x (x ': xs) = xs
  Delete x (y ': xs) = y ': Delete x xs
  Delete x '[] = '[]

-- | Consider a certain type, discarding it as an option if it is not the
-- correct one.
consider :: forall x xs. (x `HasTagIn` xs) => Sum xs -> Either (Sum (Delete x xs)) x
consider (UnsafeInj tag' x) =
  if tag' == tag @x @xs
    then Right (unsafeCoerce x)
    else Left (UnsafeInj (if tag' >= tag @x @xs then tag' - 1 else tag') x)
{-# INLINE CONLIKE consider #-}

-- | Consider the first type in the list of possibilities, a useful
-- specialization for type inference.
considerFirst :: forall x xs. Sum (x ': xs) -> Either (Sum xs) x
considerFirst = consider
{-# INLINE CONLIKE considerFirst #-}

-- | Transforms one type in the sum into another.
inmap :: forall x y xs. (x `HasTagIn` xs, y `HasTagIn` xs) => (x -> y) -> Sum xs -> Sum xs
inmap f uv@(UnsafeInj tag' x) = if tag' == tag @x @xs then UnsafeInj (tag @y @xs) (unsafeCoerce (f (unsafeCoerce x))) else uv
{-# INLINE CONLIKE inmap #-}

-- | Transform one type in one sum into another type in another sum.
smap :: forall x y xs ys. (Weaken xs ys, x `HasTagIn` xs, y `HasTagIn` ys) => (x -> y) -> Sum xs -> Sum ys
smap f uv@(UnsafeInj tag' x) = if tag' == tag @x @xs then UnsafeInj (tag @y @ys) (unsafeCoerce (f (unsafeCoerce x))) else weaken uv
{-# INLINE CONLIKE smap #-}

-- | A class which checks that every type has the same tag in the first
-- list as the second. In other words, checks if the first list is a prefix
-- of the other.
class HaveSameTagsIn xs ys
instance {-# OVERLAPPABLE #-} HaveSameTagsIn '[] ys
instance {-# OVERLAPPABLE #-} HaveSameTagsIn xs ys => HaveSameTagsIn (x ': xs) (x ': ys)

-- | A free version of weakening, where all you're doing is adding
-- more possibilities at exclusively higher tags.
noOpWeaken :: forall xs ys. (xs `HaveSameTagsIn` ys) => Sum xs -> Sum ys
noOpWeaken = unsafeCoerce
{-# INLINE CONLIKE noOpWeaken #-}

unsafeForget :: Sum (x ': xs) -> Sum xs
unsafeForget (UnsafeInj tag' x) = UnsafeInj (tag' - 1) x
{-# INLINE CONLIKE unsafeForget #-}

-- | Testing extensible sums for equality.
instance (Eq (Sum xs), Eq x) => Eq (Sum (x ': xs)) where
  uv@(UnsafeInj tag' x) == uv'@(UnsafeInj tag'' x')
    | tag' == tag'' =
        if tag' == 0
          then unsafeCoerce @_ @x x == unsafeCoerce @_ @x x'
          else unsafeForget uv == unsafeForget uv'
    | otherwise = False
  {-# INLINE CONLIKE (==) #-}
instance Eq (Sum '[]) where
  (==) = error "(==) base case: impossible by construction"

-- | Transforming one sum into a sum which contains all of the same types
class Weaken xs ys where
  weaken :: Sum xs -> Sum ys
instance (Weaken xs ys, x `HasTagIn` ys) => Weaken (x ': xs) ys where
  weaken uv@(UnsafeInj tag' x) =
    if tag' == 0
      then UnsafeInj (tag @x @ys) x
      else let UnsafeInj tag'' _ = weaken @xs @ys (unsafeForget uv) in UnsafeInj tag'' x
  {-# INLINE CONLIKE weaken #-}
instance Weaken '[] ys where
  weaken = error "weaken base case: impossible by construction"
  {-# INLINE CONLIKE weaken #-}

-- | The scott encoding of an extensible sum
type family Matcher xs r :: Type where
  Matcher '[] r = r
  Matcher (x ': xs) r = (x -> r) -> Matcher xs r

-- | A typeclass for scott encoding extensible sums
class Match xs where
  match :: forall r. Sum xs -> Matcher xs r
  unmatch :: (forall r. Matcher xs r) -> Sum xs
  override :: forall r. r -> Matcher xs r -> Matcher xs r
instance Match '[] where
  match = error "match base case: impossible by construction"
  {-# INLINE CONLIKE match #-}
  unmatch = id
  {-# INLINE CONLIKE unmatch #-}
  override = const
  {-# INLINE CONLIKE override #-}
instance (Unmatch xs (x ': xs), Match xs) => Match (x ': xs) where
  match :: forall r. Sum (x ': xs) -> (x -> r) -> Matcher xs r
  match uv@(UnsafeInj tag' x) f =
    if tag' == 0
      then override @xs @r (f (unsafeCoerce x)) $ match @xs @r (unsafeForget uv)
      else match @xs @r (unsafeForget uv)
  {-# INLINE CONLIKE match #-}
  unmatch :: (forall r. (x -> r) -> Matcher xs r) -> Sum (x ': xs)
  unmatch g = unmatchGo @xs $ g @(Sum (x ': xs)) (UnsafeInj 0 . unsafeCoerce @x)
  {-# INLINE CONLIKE unmatch #-}
  override r m = fmap (override @xs r) m
  {-# INLINE CONLIKE override #-}

class Unmatch xs ys where
  unmatchGo :: Matcher xs (Sum ys) -> Sum ys
instance Unmatch '[] ys where
  unmatchGo = id
instance (Unmatch xs ys, x `HasTagIn` ys) => Unmatch (x ': xs) ys where
  unmatchGo f = unmatchGo @xs (f (UnsafeInj (tag @x @ys) . unsafeCoerce @x))

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
