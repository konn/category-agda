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
             ; identityL   = λ{A} {B} {f} → identityL {A} {B} {f}
             ; identityR   = λ{A} {B} {f} → identityR {A} {B} {f}
             ; o-resp-≈    = λ{A} {B} {C} {P} {Q} {R} {S} → o-resp-≈ {A}{B}{C}{P}{Q}{R}{S}
             ; associative = λ {A} {B} {C} {D} {P} {Q} {R} → associative {A} {B} {C} {D} {P} {Q} {R} 
             }
      where
        identityL : {A B : RelObj ℓ} {P : A -Rel⟶ B} → (RelId ∘ P) ≈ P
        identityL {A} {B} {P} = exactly lhs rhs
          where
            lhs : ∀{i : A} {j : B} → (RelId ∘ P) i j → P i j
            lhs {i} {j} (Comp {a = ReflRel} {b = Pij}) = Pij
            rhs : ∀{i : A} {j : B} → P i j → (RelId ∘ P) i j
            rhs {i} {j} (Pij) = Comp {j = j} {ReflRel} {Pij}
        identityR : {A B : RelObj ℓ} {P : A -Rel⟶ B} → (P ∘ RelId) ≈ P
        identityR {A} {B} {P} = exactly lhs rhs
          where
            lhs : ∀{i : A} {j : B} → (P ∘ RelId) i j → P i j
            lhs (Comp {a = Pij} {b = ReflRel}) = Pij
            rhs : ∀{i : A} {j : B} → P i j → (P ∘ RelId) i j
            rhs {i} Pij = Comp {j = i} {Pij} {ReflRel}

        o-resp-≈ : {A B C : RelObj ℓ} {P Q : A -Rel⟶ B} {R S : B -Rel⟶ C}
                 → P ≈ Q → R ≈ S → (R ∘ P) ≈ (S ∘ Q)
        o-resp-≈ {A} {B} {C} {P = P} {Q} {R} {S} (exactly P⇒Q Q⇒P) (exactly R⇒S S⇒R)
          = exactly lhs rhs
          where
            lhs : ∀ {i : A} {j : C} → (R ∘ P) i j → (S ∘ Q) i j
            lhs {i} {j} (Comp {a = Rkj} {b = Pik} ) = Comp {a = R⇒S Rkj} {b = P⇒Q Pik}
            rhs : S ∘ Q ⇒ R ∘ P
            rhs {i} {j} (Comp {a = Skj} {b = Qik} ) = Comp {a = S⇒R Skj} {b = Q⇒P Qik}

        associative : {A B C D : RelObj ℓ} {P : C -Rel⟶ D} {Q : B -Rel⟶ C} {R : A -Rel⟶ B}
                    → (P ∘ (Q ∘ R)) ≈ ((P ∘ Q) ∘ R)
        associative {A} {B} {C} {D} {P} {Q} {R} = exactly lhs rhs
          where
            lhs : ∀{i : A} {l : D} → (P ∘ (Q ∘ R)) i l → ((P ∘ Q) ∘ R) i l
            lhs {i} {l} (Comp {a = Pkl} {b = QRik}) = Comp {{!!}} {{!!}}
            rhs : ∀{i : A} {l : D} → ((P ∘ Q) ∘ R) i l → (P ∘ (Q ∘ R)) i l
            rhs {i} {l} (Comp {a = PQjl} {b = Rij}) = Comp {{!!}} {{!!}}
