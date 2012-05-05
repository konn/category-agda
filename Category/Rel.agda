{-# OPTIONS --universe-polymorphism #-}
module Category.Rel where
open import Category
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.Core
open import Relation.Binary
open import Level

RelObj : ∀ ℓ → Set (suc ℓ)
RelObj ℓ = Set ℓ

_-Rel⟶_ : ∀{ℓ} → RelObj ℓ → RelObj ℓ → Set _
_-Rel⟶_ {ℓ} A B = REL A B (suc ℓ)

data RelId {ℓ} {A : RelObj ℓ} (x : A) : A → Set (suc ℓ) where
  ReflRel : RelId x x

data _∘_ {ℓ} {A B C : RelObj ℓ} (P : B -Rel⟶ C ) (Q : A -Rel⟶ B) (i : A) (k : C) : Set (suc ℓ) where
  Comp : {j : B} → {a : P j k} → {b : Q i j} → _∘_ P Q i k

Rels : ∀{ℓ} → Category _ _ _
Rels {ℓ} = record { Obj = RelObj ℓ
                  ; Hom = _-Rel⟶_
                  ; _o_ = _∘_
                  ; _≈_ = _≡_
                  ; isCategory = isCategory
                  }
  where
    isCategory : IsCategory (RelObj ℓ) _-Rel⟶_ _≡_ _∘_ RelId
    isCategory =
      record {}

