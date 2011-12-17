{-# OPTIONS --universe-polymorphism #-}
import Category

module Category.Isomorphism {c₁ c₂ ℓ} (C : Category.Category c₁ c₂ ℓ) where
open Category.Category C
open import Level

record _≅_ (A : Obj)  (B : Obj) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  field
    f : Hom A B
    g : Hom B A
    isoA : f o g ≈ Id {B}
    isoB : g o f ≈ Id {A}
