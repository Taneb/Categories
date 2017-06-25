module Category.Ens where

open import Data.Product
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Category
open import Category.Product

Ens : ∀ {o} → ProductCategory (suc o) o o
Ens {o} = record {
  category = record {
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
    };
  _×_ = _×_;
  π₁ = proj₁;
  π₂ = proj₂;
  <_,_> = <_,_>;
  product-comm₁ = λ _ _ _ → refl;
  product-comm₂ = λ _ _ _ → refl;
  product-unique = λ _ _ _ → λ p q x → cong₂ _,_ (p x) (q x)
  }
