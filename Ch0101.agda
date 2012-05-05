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
