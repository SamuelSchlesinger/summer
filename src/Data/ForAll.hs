{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExplicitNamespaces #-}
module Data.ForAll (type ForAll) where

import GHC.Exts (Constraint)

type family ForAll c xs :: Constraint where
  ForAll c '[] = ()
  ForAll c (x ': xs) = (c x, ForAll c xs)

