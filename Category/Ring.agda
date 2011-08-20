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

