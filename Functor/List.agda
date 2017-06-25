module Functor.List {o} where

import Data.List as L
import Data.List.Properties as L

open import Category.Ens
open import Functor (Ens {o}) (Ens {o})

List : Functor
List = record {
  ⟦_⟧ = L.List;
  ⟪_⟫ = L.map;
  ⟪⟫-cong = L.map-cong;
  preserves-id = L.map-id;
  preserves-∘ = L.map-compose
  }
