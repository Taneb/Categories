open import Category
open import Functor

module NaturalTransformation {o a ℓ} {C D : Category o a ℓ} (F G : Functor C D) where

open import Level

private
  module C = Category.Category C
  module D = Category.Category D
  module F = Functor.Functor F
  module G = Functor.Functor G

record NaturalTransformation : Set (o ⊔ a ⊔ ℓ) where
  field
    component : (α : C.Ob) → D.Mor (F.⟦ α ⟧) (G.⟦ α ⟧)
    comm : ∀ {α β} (f : C.Mor α β) → component β D.∘ F.⟪ f ⟫ D.≈ G.⟪ f ⟫ D.∘ component α
      

