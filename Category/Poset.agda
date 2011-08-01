{-# OPTIONS --universe-polymorphism #-}
module Category.Poset where
open import Category
open import Relation.Binary
open import Relation.Binary.Core
open import Level

PosetObj : ∀{c ℓ₁ ℓ₂} → (Poset c ℓ₁ ℓ₂) → Set c
PosetObj P = Poset.Carrier P


data PosetMor {c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} : PosetObj P → PosetObj P → Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  Ord : {n m : Poset.Carrier P} → Poset._≤_ P n m → PosetMor n m

PosetId : ∀{c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} {n : PosetObj P} → PosetMor {c} {ℓ₁} {ℓ₂} {P} n n
PosetId {c} {ℓ₁} {ℓ₂} {P} = Ord (IsPreorder.reflexive
                                   (IsPartialOrder.isPreorder (Poset.isPartialOrder P))
                                   (IsEquivalence.refl
                                    (IsPreorder.isEquivalence
                                     (IsPartialOrder.isPreorder (Poset.isPartialOrder P)))))

comp : ∀{c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} {A B C : PosetObj P}
  → PosetMor {c} {ℓ₁} {ℓ₂} {P} B C
  → PosetMor {c} {ℓ₁} {ℓ₂} {P} A B
  → PosetMor {c} {ℓ₁} {ℓ₂} {P} A C
comp {_} {_} {_} {P} (Ord ord₂) (Ord ord₁) =
  Ord (IsPreorder.trans (IsPartialOrder.isPreorder (Poset.isPartialOrder P)) ord₁ ord₂)

cong : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong {A} {B} f refl = refl

PosetAssoc : ∀{c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} {A B C D : PosetObj P}
             {f : PosetMor {c} {ℓ₁} {ℓ₂} {P} A B}
             {g : PosetMor {c} {ℓ₁} {ℓ₂} {P} B C}
             {h : PosetMor {c} {ℓ₁} {ℓ₂} {P} C D}
           → comp h (comp g f) ≡ comp (comp h g) f
PosetAssoc {_} {_} {_} {P} {A} {B} {C} {D} {Ord ord₁} {Ord ord₂} {Ord ord₃} =
  cong {Ord} refl

{-
PosetIdentityL : ∀{c ℓ₁ ℓ₂} {P : Poset c ℓ₁ ℓ₂} {A B : PosetObj P} {f : PosetMor {c} {ℓ₁} {ℓ₂} {P} A B}
               → comp PosetId f ≡ f
PosetIdentityL {c} {ℓ₁} {ℓ₂} {P} {A} {B} {Ord ord} = 
-}