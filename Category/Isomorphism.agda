{-# OPTIONS --universe-polymorphism #-}
import Category

module Category.Isomorphism {c₁ c₂ ℓ} (C : Category.Category c₁ c₂ ℓ) where
open Category.Category C
open import Level
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary
open import Relation.Binary.Core

record _⁻¹≈_ {A B} (f : Hom A B) (g : Hom B A) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  field
    invˡ : g o f ≈ Id
    invʳ : f o g ≈ Id

record Iso {A B : Obj} (f : Hom A B) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  field
    inverse : Hom B A
    proof : f ⁻¹≈ inverse

record _≅_ (A : Obj)  (B : Obj) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  field
    f : Hom A B
    iso : Iso f

inverse-unique : {A B : Obj} {f : Hom A B} {g g′ : Hom B A} → f ⁻¹≈ g → f ⁻¹≈ g′ → g ≈ g′
inverse-unique {f = f} {g} {g′} g-inv g′-inv =
  begin
    g             ≈⟨ ≈-sym₂ identityL ⟩
    Id o g        ≈⟨ o-resp-≈ ≈-refl (≈-sym₁ (_⁻¹≈_.invˡ g′-inv)) ⟩
    (g′ o f) o g   ≈⟨ ≈-sym₂ associative ⟩
    g′ o (f o g)   ≈⟨ o-resp-≈ (_⁻¹≈_.invʳ g-inv) ≈-refl ⟩
    g′ o Id        ≈⟨ identityR ⟩
    g′
  ∎
  where
    open EqR homsetoid
    open Category.IsCategory isCategory
    open IsEquivalence isEquivalence
      renaming (refl to ≈-refl; sym to ≈-sym₂)
    open IsEquivalence isEquivalence
      renaming (sym to ≈-sym₁)

inverse-opposite : {A B : Obj} {f : Hom A B} {g : Hom B A} → f ⁻¹≈ g → g ⁻¹≈ f
inverse-opposite iso = record { invʳ = _⁻¹≈_.invˡ iso ; invˡ = _⁻¹≈_.invʳ iso }
