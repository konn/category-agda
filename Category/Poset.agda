{-# OPTIONS --universe-polymorphism #-}
module Category.Poset where
open import Category
open import Relation.Binary
open import Relation.Binary.Core
open import Level

PosetObj : ∀{c ℓ₁ ℓ₂} → (Poset c ℓ₁ ℓ₂) → Set c
PosetObj P = Poset.Carrier P


data PosetMor {c ℓ₁ ℓ₂}  (P : Poset c ℓ₁ ℓ₂) : PosetObj P → PosetObj P → Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  Ord : {n m : Poset.Carrier P} → Poset._≤_ P n m → PosetMor P n m

PosetId : ∀{c ℓ₁ ℓ₂} → (P : Poset c ℓ₁ ℓ₂) → {n : PosetObj P} → PosetMor P n n
PosetId P = Ord (IsPreorder.reflexive
                        (IsPartialOrder.isPreorder (Poset.isPartialOrder P))
                            (IsEquivalence.refl
                                    (IsPreorder.isEquivalence
                                    (IsPartialOrder.isPreorder (Poset.isPartialOrder P)))))

_[_≦_] : ∀{c ℓ₁ ℓ₂} → (P : Poset c ℓ₁ ℓ₂) → PosetObj P → PosetObj P → Set ℓ₂
P [ n ≦ m ] = Poset._≤_ P n m

_[_≡_] : ∀{c ℓ₁ ℓ₂} → (P : Poset c ℓ₁ ℓ₂) → PosetObj P → PosetObj P → Set ℓ₁
P [ n ≡ m ] = Poset._≈_ P n m

data _≃_ {c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} {A B : PosetObj P} : PosetMor P A B → PosetMor P A B → Set (suc (ℓ₂ ⊔ (ℓ₁ ⊔ c))) where
  refl : {ord₁ ord₂ : PosetMor P A B} → ord₁ ≃ ord₂

≃-sym : ∀{c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} {A B : PosetObj P} {ord₁ ord₂ : PosetMor P A B}
      →  ord₁ ≃ ord₂ → ord₂ ≃ ord₁
≃-sym refl = refl

≃-trans : ∀{c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} {A B : PosetObj P} {ord₁ ord₂ ord₃ : PosetMor P A B}
      →  ord₁ ≃ ord₂ → ord₂ ≃ ord₃ → ord₁ ≃ ord₃
≃-trans refl refl = refl

infix 4 _[_≡_] _[_≦_]

comp : ∀{c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} {A B C : PosetObj P}
  → PosetMor P B C
  → PosetMor P A B
  → PosetMor P A C
comp {P = P} (Ord ord₂) (Ord ord₁) =
  Ord (IsPreorder.trans (IsPartialOrder.isPreorder (Poset.isPartialOrder P)) ord₁ ord₂)

CategoryFromPoset : ∀{c ℓ₁ ℓ₂} → Poset c ℓ₁ ℓ₂ → Category c (suc (ℓ₂ ⊔ (ℓ₁ ⊔ c))) (suc (ℓ₂ ⊔ (ℓ₁ ⊔ c)))
CategoryFromPoset P = record { Obj = PosetObj P
                             ; Hom = PosetMor P
                             ; _o_ = comp
                             ; _≈_ = _≃_
                             ; Id  = PosetId P
                             ; isCategory = isCategory
                             }
  where
    isCategory : IsCategory (PosetObj P) (PosetMor P) _≃_ comp (PosetId P)
    isCategory =
      record { isEquivalence = record {refl = refl; sym = ≃-sym ; trans = ≃-trans}
             ; identityL = identityL
             ; identityR = identityR
             ; associative = associative
             ; o-resp-≈ = o-resp-≈
             }
      where
        identityL : {A B : PosetObj P} {f : PosetMor P A B} → comp (PosetId P) f ≃ f
        identityL {A} {B} {Ord ord} = refl
        identityR : {A B : PosetObj P} {f : PosetMor P A B} → comp f (PosetId P) ≃ f 
        identityR = refl
        associative : {A B C D : PosetObj P} {f : PosetMor P A B} {g : PosetMor P B C} {h : PosetMor P C D}
                    → comp h (comp g f) ≃ comp (comp h g) f
        associative = refl
        o-resp-≈ : {A B C : PosetObj P} {f g : PosetMor P A B} {h i : PosetMor P B C}
                 → f ≃ g → h ≃ i → comp h f ≃ comp i g
        o-resp-≈ refl refl = refl
