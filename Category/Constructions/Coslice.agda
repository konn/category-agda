{-# OPTIONS --universe-polymorphism #-}
module Category.Constructions.Coslice where
open import Category
open import Level
open import Relation.Binary
open import Relation.Binary.Core

import Relation.Binary.EqReasoning as EqR

record CosliceObj {c₁ c₂ ℓ} (C : Category c₁ c₂ ℓ) (O : Obj C) : Set (c₁ ⊔ c₂)  where
  constructor ⟦_⟧
  field
    {X}  : Obj C
    arrow : Hom C O X

record _⟶_ {c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O : Obj C} (F G : CosliceObj C O) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  private
    f = CosliceObj.arrow F
    g = CosliceObj.arrow G
  field
    arrow : Hom C (Category.cod C f) (Category.cod C g)
    proof : C [ (C [ arrow o f ]) ≈ g ] 

_∘_ : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O : Obj C} {f g h : CosliceObj C O} → (g ⟶ h) → (f ⟶ g) → (f ⟶ h)
_∘_ {C = C} {O} {f′} {g′} {h′} ψ φ =
  record { arrow = C [ a₂ o a₁ ]
         ; proof = begin
                     (a₂ o a₁) o f   ≈⟨ symm associative ⟩
                     a₂ o (a₁ o f)   ≈⟨ o-resp-≈ φ-proof reflex ⟩
                     a₂ o g  ≈⟨ ψ-proof ⟩
                     h
                   ∎
         }
      where
        f = CosliceObj.arrow f′
        g = CosliceObj.arrow g′
        h = CosliceObj.arrow h′
        module Cat = Category.Category C
        open IsCategory Cat.isCategory
        open Cat
        a₁ = _⟶_.arrow φ
        a₂ = _⟶_.arrow ψ
        open IsEquivalence (Setoid.isEquivalence homsetoid) renaming (refl to reflex)
        open IsEquivalence (Setoid.isEquivalence homsetoid) renaming (sym to symm)
        open EqR homsetoid
        φ-proof = _⟶_.proof φ
        ψ-proof = _⟶_.proof ψ

_∼_ : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O : Obj C} {F G : CosliceObj C O} → Rel (F ⟶ G) _
_∼_ {C = C} φ ψ = Category._≈_ C (_⟶_.arrow φ) (_⟶_.arrow ψ)

CosliceId : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O : Obj C} {F : CosliceObj C O} → (F ⟶ F)
CosliceId {C = C} {O} {F = F} =
  record { arrow = Cat.Id
         ; proof = identityL
         }
  where
    module Cat = Category.Category C
    module isCat = IsCategory Cat.isCategory
    open Cat
    open isCat
    f = CosliceObj.arrow F

_\\_ : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → (O : Obj C) → Category _ _ _
_\\_ {c₁} {c₂} {ℓ} C O = record { Obj = CosliceObj C O
                               ; Hom = _⟶_ {C = C} {O}
                               ; Id  = CosliceId
                               ; _o_ = _∘_
                               ; _≈_ = _∼_
                               ; isCategory = isCategory
                               }
  where
    open Category.Category C hiding (isCategory)
    open IsCategory (Category.isCategory C)
    ∼-refl : {F G : CosliceObj C O} {φ : F ⟶ G} → φ ∼ φ
    ∼-refl = IsEquivalence.refl isEquivalence
    ∼-trans : {F G : CosliceObj C O} {φ ψ σ : F ⟶ G} → φ ∼ ψ → ψ ∼ σ → φ ∼ σ
    ∼-trans = IsEquivalence.trans isEquivalence
    ∼-sym : {F G : CosliceObj C O} {φ ψ : F ⟶ G} → φ ∼ ψ → ψ ∼ φ
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

