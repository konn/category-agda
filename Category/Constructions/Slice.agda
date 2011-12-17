{-# OPTIONS --universe-polymorphism #-}
module Category.Constructions.Slice where
open import Category
open import Level
open import Relation.Binary
open import Relation.Binary.Core

import Relation.Binary.EqReasoning as EqR

record SliceObj {c₁ c₂ ℓ} (C : Category c₁ c₂ ℓ) (O : Obj C) : Set (c₁ ⊔ c₂)  where
  constructor ⟦_⟧
  field
    {X}  : Obj C
    arrow : Hom C X O

record _⟶_ {c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O : Obj C} (F G : SliceObj C O) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  private
    f = SliceObj.arrow F
    g = SliceObj.arrow G
  field
    arrow : Hom C (Category.dom C f) (Category.dom C g)
    proof : C [ f ≈ C [ g o arrow ] ]

_∘_ : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O : Obj C} {f g h : SliceObj C O} → (g ⟶ h) → (f ⟶ g) → (f ⟶ h)
_∘_ {C = C} {O} {f′} {g′} {h′} ψ φ =
  record { arrow = C [ a₂ o a₁ ]
         ; proof = begin
                     f              ≈⟨ φ-proof ⟩
                     g o a₁         ≈⟨ o-resp-≈ reflex ψ-proof ⟩
                     (h o a₂) o a₁  ≈⟨ symm associative ⟩
                     h o (a₂ o a₁)
                   ∎
         }
      where
        f = SliceObj.arrow f′
        g = SliceObj.arrow g′
        h = SliceObj.arrow h′
        module Cat = Category.Category C
        open IsCategory Cat.isCategory
        open Cat
        a₁ = _⟶_.arrow φ
        a₂ = _⟶_.arrow ψ
        open IsEquivalence (Setoid.isEquivalence homsetoid) renaming (refl to reflex)
        open IsEquivalence (Setoid.isEquivalence homsetoid) renaming (sym to symm)
        open EqR homsetoid
        φ-proof = _⟶_.proof φ
        ψ-proof : g ≈ h o a₂
        ψ-proof = _⟶_.proof ψ

_∼_ : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O : Obj C} {F G : SliceObj C O} → Rel (F ⟶ G) _
_∼_ {C = C} φ ψ = Category._≈_ C (_⟶_.arrow φ) (_⟶_.arrow ψ)

SliceId : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O : Obj C} {F : SliceObj C O} → (F ⟶ F)
SliceId {C = C} {O} {F = F} =
  record { arrow = Cat.Id
         ; proof = ≈-sym identityR
         }
  where
    module Cat = Category.Category C
    module isCat = IsCategory Cat.isCategory
    open Cat
    open isCat
    f = SliceObj.arrow F
    module Eq = IsEquivalence (Setoid.isEquivalence homsetoid)
    open Eq renaming (sym to ≈-sym)

_/_ : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → (O : Obj C) → Category _ _ _
_/_ {c₁} {c₂} {ℓ} C O = record { Obj = SliceObj C O
                               ; Hom = _⟶_ {C = C} {O}
                               ; Id  = SliceId
                               ; _o_ = _∘_
                               ; _≈_ = _∼_
                               ; isCategory = isCategory
                               }
  where
    open Category.Category C hiding (isCategory)
    open IsCategory (Category.isCategory C)
    ∼-refl : {F G : SliceObj C O} {φ : F ⟶ G} → φ ∼ φ
    ∼-refl = IsEquivalence.refl isEquivalence
    ∼-trans : {F G : SliceObj C O} {φ ψ σ : F ⟶ G} → φ ∼ ψ → ψ ∼ σ → φ ∼ σ
    ∼-trans = IsEquivalence.trans isEquivalence
    ∼-sym : {F G : SliceObj C O} {φ ψ : F ⟶ G} → φ ∼ ψ → ψ ∼ φ
    ∼-sym = IsEquivalence.sym isEquivalence

    isCategory = record { isEquivalence = record { refl = λ{φ} → ∼-refl {φ = φ}
                                                 ; sym = λ{φ} {ψ} → ∼-sym {φ = φ} {ψ}
                                                 ; trans = λ{φ} {ψ} {σ} → ∼-trans {φ = φ} {ψ} {σ}
                                                 }
                        ; identityL = identityL
                        ; identityR = identityR
                        ; associative = associative
                        ; o-resp-≈ = o-resp-≈
                        }

