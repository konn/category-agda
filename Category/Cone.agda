{-# OPTIONS --universe-polymorphism #-}
import Category

module Category.Cone {c₁ c₂ ℓ} (C : Category.Category c₁ c₂ ℓ) where
open Category.Category C
open import Level
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary
open import Relation.Binary.Core

record Diagram {c₁′ c₂′ ℓ′} (J : Category.Category c₁′ c₂′ ℓ′) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    type : Category.Functor J C
  index : Set c₁′
  index = Category.Category.Obj J
  edge : index → index → Set c₂′
  edge = Category.Category.Hom J

open Diagram

record Cone {c₁′ c₂′ ℓ′} {J : Category.Category c₁′ c₂′ ℓ′} (D : Diagram J) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  open Category.Functor (type D)
  field
    apex : Obj
    proj : ∀ i → Hom apex (FObj i)
    .isCone : ∀{i j : index D} {α : edge D i j } → proj j ≈ FMap α o proj i

record _-Cone⟶_ {c₁′ c₂′ ℓ′} {J : Category.Category c₁′ c₂′ ℓ′} {D : Diagram J} (C₁ : Cone D) (C₂ : Cone D)
         : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  -- private
  open Cone
  field
    morphism : Hom (apex C₁) (apex C₂)
    .isConeMorphism : ∀ {j} → proj C₁ j ≈ proj C₂ j o morphism
  
open Cone
open _-Cone⟶_

ConeId : ∀{c₁′ c₂′ ℓ′} {J : Category.Category c₁′ c₂′ ℓ′} {D : Diagram J} {C₁ : Cone D} → C₁ -Cone⟶ C₁
ConeId {C₁ = C₁} =
  record { morphism = Id { apex C₁ } ; isConeMorphism = proof }
  where
    .proof : ∀ {j} → proj C₁ j ≈ proj C₁ j o Id
    proof = ≈-sym identityR
      where open Category.IsCategory isCategory
            open IsEquivalence isEquivalence renaming (sym to ≈-sym)


    
_∘_ : ∀ {c₁′ c₂′ ℓ′} {J : Category.Category c₁′ c₂′ ℓ′} {D : Diagram J} {C₁ C₂ C₃ : Cone D}
   → C₂ -Cone⟶ C₃ → C₁ -Cone⟶ C₂ → C₁ -Cone⟶ C₃
_∘_ {D = D} {C₁} {C₂} {C₃} C₂toC₃ C₁toC₂ =
  record { morphism = morph ; isConeMorphism = proof }
  where
    morph = morphism C₂toC₃ o morphism C₁toC₂
    .proof : {j : index D} → proj C₁ j ≈ proj C₃ j o (morphism C₂toC₃ o morphism C₁toC₂)
    proof {j} =
      begin
        proj C₁ j                                       ≈⟨ isConeMorphism C₁toC₂ ⟩
        proj C₂ j o morphism C₁toC₂                      ≈⟨ o-resp-≈ ≈-refl (isConeMorphism C₂toC₃) ⟩
        (proj C₃ j o morphism C₂toC₃) o morphism C₁toC₂   ≈⟨ ≈-sym associative ⟩
        proj C₃ j o (morphism C₂toC₃ o morphism C₁toC₂)
      ∎
      where open Category.IsCategory isCategory
            open IsEquivalence isEquivalence
              renaming (refl to ≈-refl)
            open IsEquivalence isEquivalence
              renaming (sym to ≈-sym)
            open EqR homsetoid
