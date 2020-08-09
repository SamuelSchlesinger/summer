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
  , pattern Variant
  -- * Construction and deconstruction of extensible sums
  , inject
  , inspect
  , consider
  -- * Type family to compute the tag of a type in a type level list
  , TagIn
  , HasTagIn
  -- * Weakening extensible sums
  , Weaken(weaken)
  , noOpWeaken
  , HaveSameTagsIn
  -- * Transforming the insides of extensible sums
  , inmap
  , smap
  -- * Matching on extensible sums in the style of 'maybe' or 'either'
  , Matcher
  , Match(match, override)
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
data Sum (xs :: [*]) = UnsafeVariant !Word Any

type role Sum representational

-- | A pattern to match on for convenience. Without this, the user facing
-- interface is rather baroque.
pattern Variant :: forall x xs. (x `HasTagIn` xs) => x -> Sum xs
pattern Variant x <- (inspect -> Just x)
  where
    Variant x = inject x

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

-- | Injects a type into the extensible sum.
inject :: forall x xs. (x `HasTagIn` xs) => x -> Sum xs
inject x = UnsafeVariant (tag @x @xs) (unsafeCoerce x)

-- | Inspects an extensible sum for a particular type.
inspect :: forall x xs. (x `HasTagIn` xs) => Sum xs -> Maybe x
inspect (UnsafeVariant tag' x) = if tag @x @xs == tag' then Just (unsafeCoerce x) else Nothing

-- | Consider a certain type, discarding it as an option if it is not the
-- correct one.
consider :: forall x xs. Sum (x ': xs) -> Either (Sum xs) x
consider (UnsafeVariant tag' x) = if tag' == 0 then Right (unsafeCoerce x) else Left (UnsafeVariant (tag' - 1) x)

-- | Transforms one type in the sum into another.
inmap :: forall x y xs. (x `HasTagIn` xs, y `HasTagIn` xs) => (x -> y) -> Sum xs -> Sum xs
inmap f uv@(UnsafeVariant tag' x) = if tag' == tag @x @xs then UnsafeVariant (tag @y @xs) (unsafeCoerce (f (unsafeCoerce x))) else uv

-- | Transform one type in one sum into another type in another sum.
smap :: forall x y xs ys. (Weaken xs ys, x `HasTagIn` xs, y `HasTagIn` ys) => (x -> y) -> Sum xs -> Sum ys
smap f uv@(UnsafeVariant tag' x) = if tag' == tag @x @xs then UnsafeVariant (tag @y @ys) (unsafeCoerce (f (unsafeCoerce x))) else weaken uv



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

-- | Testing extensible sums for equality.
instance (Eq (Sum xs), Eq x) => Eq (Sum (x ': xs)) where
  UnsafeVariant tag' x == UnsafeVariant tag'' x'
    | tag' == tag'' = if tag' == 0 then unsafeCoerce @_ @x x == unsafeCoerce @_ @x x' else UnsafeVariant @xs (tag' - 1) x == UnsafeVariant @xs (tag'' - 1) x'
    | otherwise = False
instance Eq (Sum '[]) where
  (==) = error "(==) base case: impossible by construction"

-- | Transforming one sum into a sum which contains all of the same types
class Weaken xs ys where
  weaken :: Sum xs -> Sum ys
instance {-# OVERLAPPABLE #-} (Weaken xs ys, x `HasTagIn` ys) => Weaken (x ': xs) ys where
  weaken uv@(UnsafeVariant tag' x) =
    if tag' == 0
      then UnsafeVariant (tag @x @ys) x
      else let UnsafeVariant tag'' _ = weaken @xs @ys (UnsafeVariant (tag' - 1) x) in UnsafeVariant tag'' x
instance {-# OVERLAPPABLE #-} Weaken '[] ys where
  weaken = error "weaken base case: impossible by construction"

-- | The scott encoding of an extensible sum
type family Matcher xs r :: Type where
  Matcher '[] r = r
  Matcher (x ': xs) r = (x -> r) -> Matcher xs r

-- | A typeclass for scott encoding extensible sums
class Match xs where
  match :: forall r. Sum xs -> Matcher xs r
  override :: forall r. r -> Matcher xs r -> Matcher xs r
instance Match '[] where
  match = error "match base case: impossible by construction"
  override = const
instance Match xs => Match (x ': xs) where
  match :: forall r. Sum (x ': xs) -> (x -> r) -> Matcher xs r
  match (UnsafeVariant tag' x) f =
    if tag' == 0
      then override @xs @r (f (unsafeCoerce x)) $ match @xs @r (UnsafeVariant (tag' - 1) x)
      else match @xs @r (UnsafeVariant (tag' - 1) x)
  override r m = fmap (override @xs r) m

test :: IO ()
test = catchAndDisplay
  [ tagTest
  , eqTest
  , noOpWeakenTest
  , weakenTest
  , matchTest
  , considerTest
  , inmapTest
  , smapTest
  ]
  where
    catchAndDisplay (x : xs) = catch @SomeException x print >> catchAndDisplay xs
    catchAndDisplay [] = pure ()
    tagTest = do
      let tag' = tag @Int @'[Bool, Int]
          tag'' = tag @Bool @'[Bool, Int]
      unless (tag' == 1) $ fail ("Tag " <> show tag' <> " does not equal 1")
    eqTest = do
      let x :: Sum '[Int, Bool] = Variant (10 :: Int)
          y :: Sum '[Int, Bool] = Variant True
          z :: Sum '[Int, Bool] = Variant (11 :: Int)
          -- wrap around the alphabet like fromIntegral
          a :: Sum '[Int, Bool] = Variant (10 :: Int)
          b :: Sum '[Int, Bool] = Variant False
          c :: Sum '[Int, Bool] = Variant True
      unless (x /= y) $ fail "10 equals True"
      unless (x /= z) $ fail "10 equals 11"
      unless (x == a) $ fail "10 does not equal 10"
      unless (y /= b) $ fail "True equals False"
      unless (y == c) $ fail "True does not equal True"
    noOpWeakenTest = do
      let x :: Sum '[Int, Bool]  = Variant (10 :: Int)
          y :: Sum '[Int, Bool, Integer] = noOpWeaken x
      unless (y == Variant (10 :: Int)) $ fail "y does not equal Variant 10"
      pure ()
    weakenTest = do
      let x :: Sum '[Int, Bool] = Variant (10 :: Int)
          y :: Sum '[Bool, Int] = weaken x
          z :: Sum '[Integer, Bool, Float, Int] = weaken y
      unless (y == Variant (10 :: Int)) $ fail "y does not equal Variant 10"
      unless (z == Variant (10 :: Int)) $ fail "y does not equal Variant 10"
    matchTest = do
      let x :: Sum '[Int, Bool] = Variant (10 :: Int)
      unless (match x (== 10) id) $ fail "x does not match 10"
    considerTest = do
      let x :: Sum '[Int, Bool] = Variant (10 :: Int)
          y :: Sum '[Int, Bool] = Variant True
      unless (consider x == Right 10) $ fail "x is not considered to be 10"
      unless (consider y == Left (Variant True)) $ fail $ "x is not considered to be Left (Variant True)"
    inmapTest = do
      let x :: Sum '[Int, Bool] = Variant (10 :: Int)
          y :: Sum '[Int, Bool] = inmap (== (10 :: Int)) x
          z :: Sum '[Int, Bool] = inmap (== True) x
      unless (y == Variant True) $ fail "x did not get mapped to True"
      unless (z == Variant (10 :: Int)) $ fail "x did not get left alone"
    smapTest = do
      let x :: Sum '[Int, Bool] = Variant (10 :: Int)
          y :: Sum '[Bool, Int] = smap (== (10 :: Int)) x
          z :: Sum '[Bool, Int] = smap (== True) x
      unless (y == Variant True) $ fail "x did not get mapped to True"
      unless (z == Variant (10 :: Int)) $ fail "x did not get left alone"
