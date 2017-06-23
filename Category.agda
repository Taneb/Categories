module Category where

open import Level
open import Relation.Binary

record Category o a ℓ : Set (suc (o ⊔ a ⊔ ℓ)) where
  infixl 7 _∘_
  infix 4 _≈_
  field
    Ob : Set o
    Mor : Ob → Ob → Set a
    _≈_ : ∀ {α β} → Rel (Mor α β) ℓ
    _∘_ : {α β γ : Ob} → Mor β γ → Mor α β → Mor α γ
    id : {α : Ob} → Mor α α
    isEquivalence : ∀ {α β} → IsEquivalence (_≈_ {α} {β})
    identityˡ : ∀ {α β} (g : Mor α β) → id ∘ g ≈ g
    identityʳ : ∀ {α β} (f : Mor α β) → f ∘ id ≈ f
    assoc : ∀ {α β γ δ} (f : Mor γ δ) (g : Mor β γ) (h : Mor α β) → f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
    ∘-cong : ∀ {α β γ} → (_∘_ {α} {β} {γ}) Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_

