{-# OPTIONS --universe-polymorphism #-}
module Category.Rel where
open import Category
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.Core
open import Relation.Binary
open import Level
open import Data.Product

RelObj : ∀ ℓ → Set (suc ℓ)
RelObj ℓ = Set ℓ

_-Rel⟶_ : ∀{ℓ} → RelObj ℓ → RelObj ℓ → Set _
_-Rel⟶_ {ℓ} A B = REL A B (suc ℓ)

data RelId {ℓ} {A : RelObj ℓ} (x : A) : A → Set (suc ℓ) where
  ReflRel : RelId x x

data _∘_ {ℓ} {A B C : RelObj ℓ} (P : B -Rel⟶ C ) (Q : A -Rel⟶ B) (i : A) (k : C) : Set (suc ℓ) where
  Comp : {j : B} → {a : P j k} → {b : Q i j} → _∘_ P Q i k

data _≈_ {ℓ} {A B : RelObj ℓ} (P Q : A -Rel⟶ B) : Set (suc ℓ) where
  exactly : P ⇒ Q → Q ⇒ P → P ≈ Q

≈-refl : ∀{ℓ} {A B : RelObj ℓ} {P : A -Rel⟶ B} → P ≈ P
≈-refl = exactly (λ z → z) (λ z → z)

≈-sym : ∀{ℓ} {A B : RelObj ℓ} {P Q : A -Rel⟶ B} → P ≈ Q → Q ≈ P
≈-sym (exactly P⇒Q Q⇒P) = exactly Q⇒P P⇒Q

≈-trans : ∀{ℓ} {A B : RelObj ℓ} {P Q R : A -Rel⟶ B}
        → P ≈ Q → Q ≈ R → P ≈ R
≈-trans (exactly P⇒Q Q⇒P) (exactly Q⇒R R⇒Q)
  = exactly (λ z → Q⇒R (P⇒Q z)) (λ z → Q⇒P (R⇒Q z))

Rels : ∀{ℓ} → Category _ _ (suc ℓ)
Rels {ℓ} = record { Obj = RelObj ℓ
                  ; Hom = _-Rel⟶_
                  ; _o_ = _∘_
                  ; _≈_ = _≈_
                  ; isCategory = isCategory
                  }
  where
    isCategory : IsCategory (RelObj ℓ) _-Rel⟶_ _≈_ _∘_ RelId
    isCategory =
      record { isEquivalence = record { refl = ≈-refl ; trans = ≈-trans ; sym = ≈-sym}
             ; identityL = λ{A} {B} {f} → identityL {A} {B} {f}
             }
      where
        identityL : {A B : RelObj ℓ} {P : A -Rel⟶ B} → (RelId ∘ P) ≈ P
        identityL {A} {B} {P} = exactly lhs rhs
          where
            lhs : ∀{i : A} {j : B} → (RelId ∘ P) i j → P i j
            lhs = {!!}
            rhs : ∀{i : A} {j : B} → P i j → (RelId ∘ P) i j
            rhs = λ z → Comp {ℓ} {A} {B} {B}

