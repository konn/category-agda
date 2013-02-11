{-# OPTIONS --universe-polymorphism #-}
import Category

module Category.Cone {c₁ c₂ ℓ} (C : Category.Category c₁ c₂ ℓ) where
open Category.Category C
open import Level
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary
open import Relation.Binary.Core

Diagram : ∀ {c₁′ c₂′ ℓ′} → (J : Category.Category c₁′ c₂′ ℓ′) → Set _
Diagram J = Category.Functor J C

record Cone {c₁′ c₂′ ℓ′} {J : Category.Category c₁′ c₂′ ℓ′} (D : Diagram J) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  private
    module JC = Category.Category J
    edge = JC.Hom
    index = JC.Obj
    open Category.Functor D
  field
    apex : Obj
    proj : (i : index) → Hom apex (FObj i)
    isCone : {i j : index} {α : edge i j } → proj j ≈ FMap α o proj i

record _-Cone⟶_ {c₁′ c₂′ ℓ′} {J : Category.Category c₁′ c₂′ ℓ′} {D : Diagram J} (C : Cone D) (C′ : Cone D)
         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  private
    open Cone
  field
    morphism : Hom (apex C) (apex C′)
    isConeMorphism : {j : Category.Category.Obj J} → proj C j ≈ proj C′ j o morphism
  
open Cone
open _-Cone⟶_

_∘_ : ∀ {c₁′ c₂′ ℓ′} {J : Category.Category c₁′ c₂′ ℓ′} {D : Diagram J} {C₁ C₂ C₃ : Cone D}
   → C₂ -Cone⟶ C₃ → C₁ -Cone⟶ C₂ → C₁ -Cone⟶ C₃
_∘_ {J = J} {D} {C₁} {C₂} {C₃} C₂toC₃ C₁toC₂ =
  record { morphism = morph ; isConeMorphism = proof }
  where
    open Category.IsCategory isCategory
    open IsEquivalence isEquivalence
      renaming (refl to ≈-refl)
    open IsEquivalence isEquivalence
      renaming (sym to ≈-sym)
    module JC = Category.Category J
    morph = morphism C₂toC₃ o morphism C₁toC₂
    open EqR homsetoid
    proof : ∀{j : Category.Category.Obj J} → proj C₁ j ≈ proj C₃ j o morph
    proof {j} =
      begin
        proj C₁ j                                       ≈⟨ isConeMorphism C₁toC₂ ⟩
        proj C₂ j o morphism C₁toC₂                      ≈⟨ o-resp-≈ ≈-refl (isConeMorphism C₂toC₃) ⟩
        (proj C₃ j o morphism C₂toC₃) o morphism C₁toC₂   ≈⟨ ≈-sym associative ⟩
        proj C₃ j o (morphism C₂toC₃ o morphism C₁toC₂)
      ∎
