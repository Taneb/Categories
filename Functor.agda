open import Category

module Functor {o a ℓ} (C D : Category o a ℓ) where

open import Level
open import Relation.Binary

private
  module C = Category.Category C
  module D = Category.Category D

record Functor : Set (o ⊔ a ⊔ ℓ) where
  field
    ⟦_⟧ : C.Ob → D.Ob
    ⟪_⟫ : ∀ {α β} → C.Mor α β → D.Mor ⟦ α ⟧ ⟦ β ⟧
    ⟪⟫-cong : ∀ {α β} → ⟪_⟫ {α} {β} Preserves C._≈_ ⟶ D._≈_
    preserves-id : ∀ {α} → ⟪ C.id {α} ⟫ D.≈ D.id {⟦ α ⟧}
    preserves-∘  : ∀ {α β γ} {f : C.Mor β γ} {g : C.Mor α β} →
                   ⟪ f C.∘ g ⟫ D.≈ ⟪ f ⟫ D.∘ ⟪ g ⟫
