module Category.Product where

open import Level
open import Relation.Binary

open import Category

record ProductCategory o a ℓ : Set (suc (o ⊔ a ⊔ ℓ)) where
  infixr 2 _×_
  field
    category : Category o a ℓ
  open Category.Category category public
  field
    _×_ : Ob → Ob → Ob
    π₁ : ∀ {α β} → Mor (α × β) α
    π₂ : ∀ {α β} → Mor (α × β) β
    <_,_> : ∀ {α β γ} → Mor α β → Mor α γ → Mor α (β × γ)
    product-comm₁ : ∀ {α β γ} (f : Mor α β) (g : Mor α γ) → π₁ ∘ < f , g > ≈ f
    product-comm₂ : ∀ {α β γ} (f : Mor α β) (g : Mor α γ) → π₂ ∘ < f , g > ≈ g
    product-unique : ∀ {α β γ} (f : Mor α β) (g : Mor α γ) (candidate : Mor α (β × γ)) →
                     π₁ ∘ candidate ≈ f → π₂ ∘ candidate ≈ g → candidate ≈ < f , g >



