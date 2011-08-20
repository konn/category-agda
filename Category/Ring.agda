{-# OPTIONS --universe-polymorphism #-}
module Category.Ring where
open import Category
open import Algebra
open import Algebra.Structures
open import Algebra.Morphism
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.Core
open import Relation.Binary
open import Level
open import Data.Product

RingObj : ∀{c ℓ} → Set (suc (c ⊔ ℓ))
RingObj {c} {ℓ} = Ring c ℓ

RingHom : ∀{c ℓ} → Set (suc (c ⊔ ℓ))
RingHom {c} {ℓ} = {R₁ R₂ : Ring c ℓ} → R₁ -Ring⟶ R₂

RingId : ∀{c ℓ} {R : Ring c ℓ} → R -Ring⟶ R
RingId {R = R} = record { ⟦_⟧ = ⟦_⟧ ; ⟦⟧-cong = ⟦⟧-cong ; +-homo = +-homo
                        ; *-homo = *-homo ; 1-homo = 1-homo
                        }
  where
    open Algebra.Ring R
    open Definitions Carrier Carrier _≈_
    ⟦_⟧ : Morphism
    ⟦_⟧ = λ x → x
    ⟦⟧-cong : ⟦_⟧ Preserves _≈_ ⟶ _≈_
    ⟦⟧-cong = λ x → x
    +-homo : Homomorphic₂ ⟦_⟧ _+_ _+_
    +-homo x y = IsEquivalence.refl isEquivalence
    *-homo : Homomorphic₂ ⟦_⟧ _*_ _*_
    *-homo x y = IsEquivalence.refl isEquivalence
    1-homo : Homomorphic₀ ⟦_⟧ 1# 1#
    1-homo = IsEquivalence.refl isEquivalence

[_]_ : ∀{c ℓ c′ ℓ′} {R₁ : Ring c ℓ} {R₂ : Ring c′ ℓ′} → R₁ -Ring⟶ R₂ → Ring.Carrier R₁ → Ring.Carrier R₂
[ f ] x = _-Ring⟶_.⟦_⟧ f x

_∘_ : ∀{c₁ ℓ₁ c₂ ℓ₂ c₃ ℓ₃} {R₁ : Ring c₁ ℓ₁} {R₂ : Ring c₂ ℓ₂} {R₃ : Ring c₃ ℓ₃}
    → R₂ -Ring⟶ R₃ → R₁ -Ring⟶ R₂ → R₁ -Ring⟶ R₃
_∘_ {R₁ = R₁} {R₂} {R₃} g f =
  record { ⟦_⟧ = ⟦_⟧ ; ⟦⟧-cong = ⟦⟧-cong ; +-homo = +-homo
         ; *-homo = *-homo ; 1-homo = 1-homo
         }
  where
    module F = Ring R₁
    module M = Ring R₂
    module T = Ring R₃
    module homo = _-Ring⟶_
    open Definitions F.Carrier T.Carrier T._≈_
    ⟦_⟧ : Morphism
    ⟦ x ⟧ = [ g ] ([ f ] x)
    ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
    ⟦⟧-cong x = homo.⟦⟧-cong g (homo.⟦⟧-cong f x)
    +-homo : Homomorphic₂ ⟦_⟧ F._+_ T._+_
    +-homo x y =
      begin
        ⟦ F._+_ x y ⟧                        ≈⟨ homo.⟦⟧-cong g (homo.+-homo f x y) ⟩
        [ g ] ( M._+_ ([ f ] x) ([ f ] y) ) ≈⟨ homo.+-homo g ([ f ] x) ([ f ] y) ⟩
        T._+_ ⟦ x ⟧ ⟦ y ⟧
      ∎
      where
        open IsEquivalence T.isEquivalence
        open EqR T.setoid
    *-homo : Homomorphic₂ ⟦_⟧ F._*_ T._*_
    *-homo x y =
      begin
        ⟦ F._*_ x y ⟧                        ≈⟨ homo.⟦⟧-cong g (homo.*-homo f x y) ⟩
        [ g ] ( M._*_ ([ f ] x) ([ f ] y) ) ≈⟨ homo.*-homo g ([ f ] x) ([ f ] y) ⟩
        T._*_ ⟦ x ⟧ ⟦ y ⟧
      ∎
      where
        open IsEquivalence T.isEquivalence
        open EqR T.setoid
    1-homo : Homomorphic₀ ⟦_⟧ F.1# T.1#
    1-homo =
      begin
        ⟦ F.1# ⟧     ≈⟨ homo.⟦⟧-cong g (homo.1-homo f) ⟩
        [ g ] M.1#  ≈⟨ homo.1-homo g ⟩
        T.1#
      ∎
      where
        open IsEquivalence T.isEquivalence
        open EqR T.setoid

_≈_ : ∀{c ℓ c′ ℓ′} {R₁ : Ring c ℓ} {R₂ : Ring c′ ℓ′} → Rel (R₁ -Ring⟶ R₂) (ℓ′ ⊔ c)
_≈_ {R₁ = R₁} {R₂} φ ψ = ∀(x : F.Carrier) → T._≈_ ([ φ ] x) ([ ψ ] x)
  where
    module F = Ring R₁
    module T = Ring R₂

≈-refl : ∀{c ℓ c′ ℓ′} {R₁ : Ring c ℓ} {R₂ : Ring c′ ℓ′} {F : R₁ -Ring⟶ R₂} → F ≈ F
≈-refl {R₁ = R₁} {F = F} _ = _-Ring⟶_.⟦⟧-cong F (IsEquivalence.refl (Ring.isEquivalence R₁))

≈-sym : ∀{c ℓ c′ ℓ′} {R₁ : Ring c ℓ} {R₂ : Ring c′ ℓ′} {F G : R₁ -Ring⟶ R₂} → F ≈ G → G ≈ F
≈-sym {R₁ = R₁} {R₂} {F} {G} F≈G x = IsEquivalence.sym (Ring.isEquivalence R₂)(F≈G x)

≈-trans : ∀{c ℓ c′ ℓ′} {R₁ : Ring c ℓ} {R₂ : Ring c′ ℓ′} {F G H : R₁ -Ring⟶ R₂}
        → F ≈ G → G ≈ H → F ≈ H
≈-trans {R₁ = R₁} {R₂} {F} {G} F≈G G≈H x = IsEquivalence.trans (Ring.isEquivalence R₂) (F≈G x) (G≈H x)

≈-isEquivalence : ∀{c ℓ c′ ℓ′} {R₁ : Ring c ℓ} {R₂ : Ring c′ ℓ′}
                → IsEquivalence {A = R₁ -Ring⟶ R₂} _≈_
≈-isEquivalence {R₁ = R₁} {R₂}  = record { refl = λ {F} → ≈-refl {R₁ = R₁} {R₂} {F}
                                         ; sym = λ{F} {G} → ≈-sym {R₁ = R₁} {R₂} {F} {G}
                                         ; trans = λ{F} {G} {H} → ≈-trans  {R₁ = R₁} {R₂} {F} {G} {H}
                                         }


RingCat : ∀{c ℓ} → Category _ _ _
RingCat {c} {ℓ} =
  record { Obj = Ring c ℓ
         ; Hom = _-Ring⟶_
         ; Id  = RingId
         ; _o_ = _∘_
         ; _≈_ = _≈_
         ; isCategory = isCategory
         }
  where
    isCategory : IsCategory (Ring c ℓ) _-Ring⟶_ _≈_ _∘_ RingId
    isCategory =
      record { isEquivalence = ≈-isEquivalence {c} {ℓ} {c} {ℓ}
             ; identityL = λ {R₁ R₂ f} → identityL {R₁} {R₂} {f}
             ; identityR = λ {R₁ R₂ f} → identityR {R₁} {R₂} {f}
             ; o-resp-≈    = λ {A} {B} {C} {f} {g} {h} {i} → o-resp-≈ {A} {B} {C} {f} {g} {h} {i}
             ; associative = λ {R₁} {R₂} {R₃} {R₄} {f} {g} {h} → associative {R₁} {R₂} {R₃} {R₄} {f} {g} {h}
             }
      where
        identityL : {R₁ R₂ : Ring c ℓ} {f : R₁ -Ring⟶ R₂} → (RingId ∘ f) ≈ f
        identityL {f = f} = ≈-refl {F = f}
        identityR : {R₁ R₂ : Ring c ℓ} {f : R₁ -Ring⟶ R₂} → (f ∘ RingId) ≈ f
        identityR {f = f} = ≈-refl {F = f}
        o-resp-≈ : {R₁ R₂ R₃ : Ring c ℓ} {f g : R₁ -Ring⟶ R₂} {h i : R₂ -Ring⟶ R₃}
                 → f ≈ g → h ≈ i → (h ∘ f) ≈ (i ∘ g)
        o-resp-≈ {R₃ = R₃} {f} {g} {h} {i} f≈g h≈i x =
          begin
            ([ h ∘ f ] x)     ≈⟨ h≈i ([ f ] x) ⟩
            ([ i ∘ f ] x)     ≈⟨ _-Ring⟶_.⟦⟧-cong i (f≈g x) ⟩
            ([ i ∘ g ] x)
          ∎
          where
            module T = Ring R₃
            open IsEquivalence T.isEquivalence
            open EqR T.setoid
        associative : {R₁ R₂ R₃ R₄ : Ring c ℓ} {f : R₃ -Ring⟶ R₄} {g : R₂ -Ring⟶ R₃} {h : R₁ -Ring⟶ R₂}
                    → (f ∘ (g ∘ h)) ≈ ((f ∘ g) ∘ h)
        associative {f = f} {g} {h} = ≈-refl {F = f ∘ (g ∘ h)}

        
