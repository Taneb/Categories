module Functor.List {o} where

import Data.List as L
import Data.List.Properties as L

open import Category.Product
import Category.Ens
Ens = ProductCategory.category (Category.Ens.Ens {o})
open import Functor Ens Ens

List : Functor
List = record {
  ⟦_⟧ = L.List;
  ⟪_⟫ = L.map;
  ⟪⟫-cong = L.map-cong;
  preserves-id = L.map-id;
  preserves-∘ = L.map-compose
  }
