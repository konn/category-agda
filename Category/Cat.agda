{-# OPTIONS --universe-polymorphism #-}
module Category.Cat where
open import Category
open import Level
open import Relation.Binary
open import Relation.Binary.Core

identityFunctor : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → Functor C C
identityFunctor {C = C} =
  record { FObj      = λ x → x
         ; FMap      = λ x → x
         ; isFunctor = isFunctor
         }
  where
    isFunctor : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → IsFunctor C C (λ x → x) (λ x → x)
    isFunctor {C = C} =
      record { ≈-cong   = λ x → x
             ; identity = IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C))
             ; distr    = IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C))
             }

open Functor

data [_]_~_ {c₁ c₂ ℓ} (C : Category c₁ c₂ ℓ) {A B : Obj C} (f : Hom C A B)
     : ∀{X Y : Obj C} → Hom C X Y → Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
  refl : {g : Hom C A B} → (eqv : C [ f ≈ g ]) → [ C ] f ~ g

_≃_ : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′}
    → (F G : Functor C D) → Set (suc ℓ′ ⊔ (suc c₂′ ⊔ (suc c₁′ ⊔ (c₂ ⊔ c₁))))
_≃_ {C = C} {D = D} F G = ∀{A B : Obj C} → (f : Hom C A B) → [ D ] FMap F f ~ FMap G f


_○_ : ∀{c₁ c₂ ℓ c₁′ c₂′ ℓ′ c₁″ c₂″ ℓ″} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {E : Category c₁″ c₂″ ℓ″}
      → Functor D E → Functor C D → Functor C E
_○_ {C = C} {D = D} {E = E} G F =
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

CatIsCategory : ∀{c₁ c₂ ℓ}
  → IsCategory {suc (c₁ ⊔ c₂ ⊔ ℓ)} {suc (ℓ ⊔ (c₂ ⊔ c₁))} {suc (ℓ ⊔ c₁ ⊔ c₂)} (Category c₁ c₂ ℓ) Functor _≃_ _○_ identityFunctor
CatIsCategory {c₁} {c₂} {ℓ} =
  record { isEquivalence = isEquivalence
         ; o-resp-≈    = λ {A} {B} {C} {f} {g} {h} {i} →  o-resp-≈ {A} {B} {C} {f} {g} {h} {i}
         ; identityL   = λ {C} {D} {f} → identityL {C} {D} {f}
         ; identityR   = λ {C} {D} {f} → identityR {C} {D} {f}
         ; associative = λ {C} {D} {E} {F} {f} {g} {h} → associative {C} {D} {E} {F} {f} {g} {h}
         }
  where
    isEquivalence : {C D : Category c₁ c₂ ℓ} → IsEquivalence {_} {_} {Functor C D} _≃_
    isEquivalence {C} {D} =
      record { refl  = λ {F} → ≃-refl {F}
             ; sym   = λ {F} {G} → ≃-sym {F} {G}
             ; trans = λ {F} {G} {H} → ≃-trans {F} {G} {H}
             }
      where
        ≃-refl : {F : Functor C D} → F ≃ F
        ≃-refl {F} {A} {B} f =
          refl {C = D} (IsFunctor.≈-cong (isFunctor F)
                                         (IsEquivalence.refl
                                         (IsCategory.isEquivalence (Category.isCategory C))))
    
        ≃-sym : {F G : Functor C D} → F ≃ G → G ≃ F
        ≃-sym {F} {G} F≃G {A} {B} f = helper (F≃G f)
          where
            helper : ∀{a b c d} {f : Hom D a b} {g : Hom D c d} → [ D ] f ~ g → [ D ] g ~ f
            helper (refl Ff≈Gf) = refl {C = D} (IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory D)) Ff≈Gf)
        ≃-trans : {F G H : Functor C D} → F ≃ G → G ≃ H → F ≃ H
        ≃-trans {F} {G} {H} F≃G G≃H {A} {B} f = helper (F≃G f) (G≃H f)
          where
            helper : ∀{O P Q R S T} {f : Hom D O P} {g : Hom D Q R } {h : Hom D S T}
                     → [ D ] f ~ g → [ D ] g ~ h → [ D ] f ~ h
            helper (refl Ff≈Gf) (refl Gf≈Hf) = refl {C = D} (IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory D)) Ff≈Gf Gf≈Hf)

    o-resp-≈ : {A B C : Category c₁ c₂ ℓ} {f g : Functor A B} {h i : Functor B C}
             → f ≃ g → h ≃ i → (h ○ f) ≃ (i ○ g)
    o-resp-≈ {B = B} {C} {F} {G} {H} {I} F≃G H≃I {P} {Q} f =
      helper {a = FObj F P} {b = FObj F Q} {c = FObj G P} {d = FObj G Q}
             {ϕ = FMap F f} {ψ = FMap G f} {π = FMap I (FMap G f) }
             (F≃G f) (H≃I (FMap G f))
      where
        helper : ∀{a b c d} {z w} {ϕ : Hom B a b} {ψ : Hom B c d} {π : Hom C z w}
               → [ B ] ϕ ~ ψ → [ C ] (FMap H ψ) ~ π → [ C ] (FMap H ϕ) ~ π
        helper (refl Ff≈Gf) (refl Hf≈If) = 
          refl {C = C} (IsEquivalence.trans
                          (IsCategory.isEquivalence (Category.isCategory C))
                          (IsFunctor.≈-cong (isFunctor H) Ff≈Gf) Hf≈If)
    identityL : {C D : Category c₁ c₂ ℓ} {f : Functor C D} → (identityFunctor ○ f) ≃ f
    identityL {C} {D} {f} {A} {B} ϕ = refl {_} (IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory D)))
    identityR : {C D : Category c₁ c₂ ℓ} {f : Functor C D} → (f ○ identityFunctor) ≃ f
    identityR {C} {D} {f} {A} {B} ϕ = refl {_} (IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory D)))
    associative : {C D E F : Category c₁ c₂ ℓ} {f : Functor E F} {g : Functor D E} {h : Functor C D}
                → (f ○ (g ○ h)) ≃ ((f ○ g) ○ h)
    associative {F = F} _ = refl (IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory F)))
    
CAT : ∀{c₁ c₂ ℓ} → Category (suc (c₁ ⊔ c₂ ⊔ ℓ)) (suc (ℓ ⊔ (c₂ ⊔ c₁))) (suc (ℓ ⊔ c₁ ⊔ c₂))
CAT {c₁} {c₂} {ℓ} =
  record { Obj = Category c₁ c₂ ℓ
         ; Hom = Functor
         ; _o_ = _○_
         ; _≈_ = _≃_
         ; Id  = identityFunctor
         ; isCategory = CatIsCategory {c₁} {c₂} {ℓ}
         }

