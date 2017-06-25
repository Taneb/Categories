module Category.Ens where

open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Category

Ens : ∀ {o} → Category (suc o) o o
Ens {o} = record {
  Ob = Set o;
  Mor = λ α β → α → β;
  _≈_ = _≗_;
  _∘_ = _∘′_;
  id = id;
  isEquivalence = λ {α β} → Setoid.isEquivalence (α →-setoid β);
  identityˡ = λ _ _ → refl;
  identityʳ = λ _ _ → refl;
  assoc = λ _ _ _ _ → refl;
  ∘-cong = λ {_ _ _} {f} p q x → trans (cong f (q x)) (p _)
  }
