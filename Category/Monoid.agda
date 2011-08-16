{-# OPTIONS --universe-polymorphism #-}
module Category.Monoid where
open import Category
open import Relation.Binary
open import Relation.Binary.Core
open import Algebra.Structures
open import Algebra
open import Level
open import Data.Product

data MonoidObj : Set1 where
  * : MonoidObj

data MonoidMor {c ℓ : Level} {M : Monoid c ℓ} : MonoidObj → MonoidObj → Set c where
  Mor : Monoid.Carrier M → MonoidMor * *

MonoidId : {c ℓ : Level} {M : Monoid c ℓ} {A : MonoidObj} → MonoidMor {c} {ℓ} {M} A A
MonoidId {_} {_} {M} {*} = Mor (Monoid.ε M)

comp : ∀{c ℓ} {M : Monoid c ℓ} {A B C : MonoidObj}
     → MonoidMor {c} {ℓ} {M} B C
     → MonoidMor {c} {ℓ} {M} A B
     → MonoidMor {c} {ℓ} {M} A C
comp {_} {_} {M} {*} {*} {*} (Mor a) (Mor b) = Mor (Monoid._∙_ M a b)

data _≃_ {c ℓ : Level} {M : Monoid c ℓ} : Rel (MonoidMor {_} {_} {M} * *) (suc (c ⊔ ℓ)) where
  Eq : {n m : Monoid.Carrier M} → (Monoid._≈_ M n m) → Mor n ≃ Mor m

moneq_refl : ∀{c ℓ} {M : Monoid c ℓ} → Reflexive (_≃_ {c} {ℓ} {M})
moneq_refl {c} {ℓ} {M} {Mor f} = Eq (IsEquivalence.refl (Monoid.isEquivalence M))

moneq_sym : ∀{c ℓ} {M : Monoid c ℓ} → Symmetric (_≃_ {c} {ℓ} {M})
moneq_sym {c} {ℓ} {M} {Mor f} {Mor g} (Eq eqv) = Eq (IsEquivalence.sym (Monoid.isEquivalence M) eqv)

moneq_trans : ∀{c ℓ} {M : Monoid c ℓ} → Transitive (_≃_ {c} {ℓ} {M})
moneq_trans {c} {ℓ} {M} {Mor f} {Mor g} (Eq eq₁) (Eq eq₂) = Eq (IsEquivalence.trans (Monoid.isEquivalence M) eq₁ eq₂)

_~_ : ∀{c ℓ} {M : Monoid c ℓ} {A B : MonoidObj} → Rel (MonoidMor {_} {_} {M} A B) (suc (c ⊔ ℓ))
_~_ {_} {_} {M} {*} {*} = _≃_
 
reflexive : ∀{c ℓ} {M : Monoid c ℓ} {A B : MonoidObj} → Reflexive (_~_ {c} {ℓ} {M} {A} {B})
reflexive {_} {_} {M} {*} {*} = moneq_refl

transitive : ∀{c ℓ} {M : Monoid c ℓ} {A B : MonoidObj} → Transitive (_~_ {c} {ℓ} {M} {A} {B})
transitive {_} {_} {M} {*} {*} = moneq_trans

symmetric : ∀{c ℓ} {M : Monoid c ℓ} {A B : MonoidObj} → Symmetric (_~_ {c} {ℓ} {M} {A} {B})
symmetric {_} {_} {M} {*} {*} = moneq_sym

isCategory : ∀{c ℓ} → (M : Monoid c ℓ) → IsCategory MonoidObj (MonoidMor {c} {ℓ} {M}) _~_ comp MonoidId
isCategory {c} {ℓ} M =
  record { isEquivalence = isEquivalence
         ; identityL = identityL
         ; identityR = identityR
         ; o-resp-≈  = o-resp-≈
         ; associative = assoc
         }
  where
    isEquivalence : {A B : MonoidObj}
                    → IsEquivalence {c} {suc (c ⊔ ℓ)} {MonoidMor A B} (_~_ {c} {ℓ} {M} {A} {B})
    isEquivalence {*} {*} = record { refl = reflexive; sym = symmetric; trans = transitive }
    o-resp-≃ : {f g h i : MonoidMor {c} {ℓ} {M} * *} → f ≃ g → h ≃ i → comp h f ≃ comp i g
    o-resp-≃ {Mor f} {Mor g} {Mor h} {Mor i} (Eq eq₁) (Eq eq₂) =
      Eq (IsSemigroup.∙-cong (IsMonoid.isSemigroup (Monoid.isMonoid M)) eq₂ eq₁)
    o-resp-≈ : {A B C : MonoidObj} {f g : MonoidMor {c} {ℓ} {M} A B} {h i : MonoidMor B C}
             → f ~ g → h ~ i → comp h f ~ comp i g
    o-resp-≈ {*} {*} {*} {f} {g} {h} = o-resp-≃
    assoc : {A B C D : MonoidObj}
        {f : MonoidMor {c} {ℓ} {M} A B} {g : MonoidMor {c} {ℓ} {M} B C} {h : MonoidMor {c} {ℓ} {M} C D}
          → comp h (comp g f) ~ comp (comp h g) f
    assoc {*} {*} {*} {*} {Mor f} {Mor g} {Mor h} =
      Eq (IsEquivalence.sym
        (IsSemigroup.isEquivalence
         (IsMonoid.isSemigroup (Monoid.isMonoid M)))
        (IsSemigroup.assoc (IsMonoid.isSemigroup (Monoid.isMonoid M)) h g
         f))

    identityL : {c ℓ : Level} {M : Monoid c ℓ} {A B : MonoidObj} {f : MonoidMor {c} {ℓ} {M} A B} → (comp MonoidId f) ~ f
    identityL {c} {ℓ} {M} {*} {*} {Mor f} = Eq {c} {ℓ} {M} (proj₁ (IsMonoid.identity (Monoid.isMonoid M)) f)

    identityR : {c ℓ : Level} {M : Monoid c ℓ} {A B : MonoidObj} {f : MonoidMor {c} {ℓ} {M} A B} → (comp f MonoidId) ~ f
    identityR {c} {ℓ} {M} {*} {*} {Mor f} = Eq {c} {ℓ} {M} (proj₂ (IsMonoid.identity (Monoid.isMonoid M)) f)



MONOID : ∀{c ℓ} → (M : Monoid c ℓ) →  Category (suc zero) c (suc (ℓ ⊔ c))
MONOID M = record { Obj = MonoidObj
                  ; Hom = MonoidMor {_} {_} {M}
                  ; _o_ = comp
                  ; _≈_ = _~_
                  ; Id  = MonoidId
                  ; isCategory = isCategory M
                  }
