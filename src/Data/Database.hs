{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Database where

import Data.Kind (Type)
import Data.Prodder

type TableDefinition = [Type]

type Table def = [Prod def]

type family FilterPred def fields where
  FilterPred def '[] = Bool
  FilterPred def (field ': fields) = Index field def -> FilterPred def fields

type family FieldsFromFilterPred def filterPred where
  FieldsFromFilterPred def Bool = '[]
  FieldsFromFilterPred def (a -> b) = IndexIn a def ': FieldsFromFilterPred def b

class FilterOn (def :: [Type]) (filterPred :: Type) where
  filterOn :: (filterPred ~ FilterPred def (FieldsFromFilterPred def filterPred)) => Table def -> filterPred -> Table def

instance FilterOn def Bool where
  filterOn p = \case
    True -> p
    False -> []

instance (HasIndexIn a def, FilterOn def xs) => FilterOn def (a -> xs) where
  filterOn table f = concat [ filterOn [ row ] (f (extract row)) | row <- table ] 
