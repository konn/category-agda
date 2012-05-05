{-# OPTIONS --universe-polymorphism #-}
module Ch0101 where
open import Category
open import Category.Sets
open import Category.Rel
open import Level
open import Relation.Binary
open import Relation.Binary.Core

GObj : ∀{ℓ} → Set ℓ → RelObj ℓ
GObj a = a

data GMap {ℓ} {A B : Set ℓ} (f : A → B) (x : A) : B → Set (suc ℓ) where
  Graph : GMap f x (f x)

GraphFunctor : ∀{ℓ} → Functor (Sets {ℓ}) (Rels {ℓ})
GraphFunctor {ℓ} = record { FObj = GObj
                          ; FMap = GMap
                          ; isFunctor = isFunctor
                          }
  where
    isFunctor : IsFunctor (Sets {ℓ}) (Rels {ℓ}) GObj GMap
    isFunctor = record { ≈-cong = ≈-cong
                       ; identity = identity
                       ; distr = distr
                       }
      where
        ≈-cong : {A B : Set ℓ} → {φ ψ : A -Set⟶ B} → φ ≡ ψ → GMap φ ≈ GMap ψ
        ≈-cong {A} {B} {φ} {.φ} refl = ≈-refl
        identity : {A : Set ℓ} → GMap (SetId {A = A}) ≈ RelId {A = A}
        identity {A} = exactly lhs rhs
          where
            lhs : {i j : A} → GMap SetId i j → RelId i j
            lhs {i} {.i} Graph = ReflRel
            rhs : {i j : A} → RelId i j -> GMap SetId i j
            rhs {i} {.i} ReflRel = Graph
        distr : {A B C : Set ℓ} {φ : A -Set⟶ B} {ψ : B -Set⟶ C}
              → (GMap (ψ o φ)) ≈ (GMap ψ ∘ GMap φ)
        distr {A} {B} {C} {φ} {ψ} = exactly lhs rhs
          where
            lhs : {i : A} {k : C} → GMap (ψ o φ) i k → (GMap ψ ∘ GMap φ) i k
            lhs {i} .{ψ (φ i)} Graph = Comp {a = Graph} {b = Graph}
            rhs : {i : A} {k : C} → (GMap ψ ∘ GMap φ) i k → GMap (ψ o φ) i k
            rhs {i} .{ψ (φ i)} (Comp {a = Graph} {Graph}) = Graph

OpObj : ∀{ℓ} → RelObj ℓ → RelObj ℓ
OpObj x = x

data  OpMap {ℓ} {A B : RelObj ℓ} (P : A -Rel⟶ B) (b : B) (a : A) : Set (suc ℓ) where
  complement : P a b → OpMap P b a

ComplementFunctor : ∀{ℓ} → Functor (Category.op (Rels {ℓ})) (Rels {ℓ})
ComplementFunctor {ℓ} = record { FObj = OpObj
                               ; FMap = OpMap
                               ; isFunctor = isFunctor
                               }
  where
    isFunctor : IsFunctor (Category.op (Rels {ℓ})) (Rels {ℓ}) OpObj OpMap
    isFunctor = record { ≈-cong = ≈-cong
                       ; identity = identity
                       ; distr = distr
                       }
      where
        ≈-cong : {A B : Set ℓ} {P Q : B -Rel⟶ A} → P ≈ Q → OpMap P ≈ OpMap Q
        ≈-cong {A} {B} {P} {Q} (exactly P⇒Q Q⇒P) = exactly lhs rhs
          where 
            lhs : {i : A} {j : B} → OpMap P i j → OpMap Q i j
            lhs (complement Pji) = complement (P⇒Q Pji)
            rhs : {i : A} {j : B} → OpMap Q i j → OpMap P i j
            rhs (complement Qji) = complement (Q⇒P Qji)

        identity : {A : Set ℓ} → OpMap (RelId {A = A}) ≈ RelId {A = OpObj A}
        identity {A} = exactly lhs rhs
          where
            lhs : {i j : A} → OpMap RelId i j → RelId i j
            lhs {i} .{i} (complement ReflRel) = ReflRel
            rhs : {i j : A} → RelId i j → OpMap RelId i j
            rhs {i} .{i} ReflRel = complement ReflRel

        distr : {A B C : Set ℓ} {P : B -Rel⟶ A} {Q : C -Rel⟶ B} → OpMap (P ∘ Q) ≈ (OpMap Q ∘ OpMap P)
        distr {A} {B} {C} {P} {Q} = exactly lhs rhs
          where
            lhs : {i : A} {k : C} → OpMap (P ∘ Q) i k → (OpMap Q ∘ OpMap P) i k
            lhs {i} {k} (complement (Comp {a = Pjk} {Qij} ))= Comp {a = complement Qij} {b = complement Pjk}
            rhs : {i : A} {k : C} → (OpMap Q ∘ OpMap P) i k → OpMap (P ∘ Q) i k
            rhs {i} {k} (Comp {a = complement Qij} {b = complement Pjk}) = complement (Comp {a = Pjk} {Qij})
