open import Category

module NaturalTransformation {o a ℓ} {C D : Category o a ℓ} where

open import Functor C D
open import Level

private
  module C = Category.Category C
  module D = Category.Category D

module _ (F G : Functor) where
  private
    module F = Functor F
    module G = Functor G

  record NaturalTransformation : Set (o ⊔ a ⊔ ℓ) where
    field
      component : (α : C.Ob) → D.Mor (F.⟦ α ⟧) (G.⟦ α ⟧)
      comm : ∀ {α β} (f : C.Mor α β) → component β D.∘ F.⟪ f ⟫ D.≈ G.⟪ f ⟫ D.∘ component α
      
