{-# OPTIONS --universe-polymorphism #-}
module Category.Cat where
open import Category
open import Level
open import Relation.Binary
open import Relation.Binary.Core

identityFunctor : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → Functor C C
identityFunctor {c₁} {c₂} {ℓ} {C} =
  record { FObj      = λ x → x
         ; FMap      = λ x → x
         ; isFunctor = isFunctor
         }
  where
    isFunctor : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → IsFunctor C C (λ x → x) (λ x → x)
    isFunctor {_} {_} {_} {C} =
      record { ≈-cong   = λ x → x
             ; identity = IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C))
             ; distr    = IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C))
             }

open Functor

_○_ : ∀{c₁ c₂ ℓ c₁′ c₂′ ℓ′ c₁″ c₂″ ℓ″} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {E : Category c₁″ c₂″ ℓ″}
      → Functor D E → Functor C D → Functor C E
_○_ {_} {_} {_} {_} {_} {_} {_} {_} {_} {C} {D} {E} G F =
  record { FObj = λ x → FObj G (FObj F x)
         ; FMap = λ x → FMap G (FMap F x)
         ; isFunctor = myIsFunctor
         }
  where 
    myIsFunctor : IsFunctor C E (λ x → FObj G (FObj F x)) (λ x → FMap G (FMap F x))
    myIsFunctor =
      record { ≈-cong   = λ x → IsFunctor.≈-cong (isFunctor G) (IsFunctor.≈-cong (isFunctor F) x)
             ; identity = IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory E))
                                              (IsFunctor.≈-cong (isFunctor G) (IsFunctor.identity (isFunctor F)))
                                              (IsFunctor.identity (isFunctor G))
             ; distr    = IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory E))
                                              (IsFunctor.≈-cong (isFunctor G) (IsFunctor.distr (isFunctor F)))
                                              (IsFunctor.distr (isFunctor G))
             }

{-
_≃_ : ∀{c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′}
    → Rel (Functor C D) (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′))
_≃_ = _
-}

CatIsCategory : ∀{c₁ c₂ ℓ}
  → IsCategory {suc (c₁ ⊔ c₂ ⊔ ℓ)} {suc (ℓ ⊔ (c₂ ⊔ c₁))} {suc (ℓ ⊔ c₁ ⊔ c₂)} (Category c₁ c₂ ℓ) Functor _≡_ _○_ identityFunctor
CatIsCategory {c₁} {c₂} {ℓ} =
  record { isEquivalence = isEquivalence 
         ; identityL = identityL
         ; identityR = _
         ; associative = _
         }
  where
    isEquivalence : {C D : Category c₁ c₂ ℓ} → IsEquivalence {_} {suc (ℓ ⊔ c₁ ⊔ c₂)} {Functor C D} _≡_
    isEquivalence {C} {D} = record { refl = refl ; sym = ≡-sym ; trans = ≡-trans }
    identityL : {C D : Category c₁ c₂ ℓ} {F : Functor C D} → identityFunctor ○ F ≡ F
    identityL {C} {D} {f} = {!!}
    

Cat : ∀{c₁ c₂ ℓ} → Category (suc (c₁ ⊔ c₂ ⊔ ℓ)) (suc (ℓ ⊔ (c₂ ⊔ c₁))) (suc (ℓ ⊔ c₁ ⊔ c₂))
Cat {c₁} {c₂} {ℓ}=
  record { Obj = Category c₁ c₂ ℓ
         ; Hom = Functor
         ; _≈_ = _≡_
         ; Id  = identityFunctor
         ; isCategory = CatIsCategory {c₁} {c₂} {ℓ}
         }