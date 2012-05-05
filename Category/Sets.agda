{-# OPTIONS --universe-polymorphism #-}
module Category.Sets where
open import Category
open import Relation.Binary.Core
open import Relation.Binary
open import Level

_o_ : ∀{ℓ} {A B C : Set ℓ} → (f : B → C) → (g : A → B) → A → C
_o_ f g x = f (g x)

_-Set⟶_ : ∀{ℓ} → (A B : Set ℓ) → Set _
A -Set⟶ B = A → B

SetId : ∀{ℓ} {A : Set ℓ} → A → A
SetId x = x

Sets : ∀{ℓ} → Category _ _ ℓ
Sets {ℓ} = record { Obj = Set ℓ
                  ; Hom = _-Set⟶_
                  ; _o_ = _o_
                  ; _≈_ = _≡_
                  ; isCategory = isCategory
                  }
  where
    isCategory : IsCategory (Set ℓ) _-Set⟶_ _≡_ _o_ SetId
    isCategory = record { isEquivalence = record {refl = refl ; trans = ≡-trans ; sym = ≡-sym}
                        ; identityL     = refl
                        ; identityR     = refl
                        ; o-resp-≈      = o-resp-≈
                        ; associative   = refl
                        }
      where
        o-resp-≈ : {A B C : Set ℓ} {f g : A -Set⟶ B} {h i : B -Set⟶ C}
                 → f ≡ g → h ≡ i → h o f ≡ i o g
        o-resp-≈ refl refl = refl
