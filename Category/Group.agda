{-# OPTIONS --universe-polymorphism #-}
module Category.Group where
open import Category
open import Algebra
open import Algebra.Structures
open import Algebra.Morphism
import Algebra.Props.Group as GroupP
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.Core
open import Relation.Binary
open import Level
open import Data.Product

GrpObj : ∀{c ℓ} → Set (suc (c ⊔ ℓ))
GrpObj {c} {ℓ} = Group c ℓ

record _-Group⟶_ {c ℓ c′ ℓ′} (From : Group c ℓ) (To : Group c′ ℓ′) : Set (c ⊔ ℓ ⊔ c′ ⊔ ℓ′) where
  private 
    module F = Group From
    module T = Group To
  open Definitions F.Carrier T.Carrier T._≈_
  field
    ⟦_⟧ : Morphism
    ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
    ∙-homo : Homomorphic₂ ⟦_⟧ F._∙_ T._∙_
  
  ε-homo : Homomorphic₀ ⟦_⟧ F.ε T.ε
  ε-homo = left-identity-unique ⟦ F.ε ⟧ ⟦ F.ε ⟧ (begin
    T._∙_ ⟦ F.ε ⟧ ⟦ F.ε ⟧ ≈⟨ T.sym (∙-homo F.ε F.ε) ⟩
    ⟦ F._∙_ F.ε F.ε ⟧ ≈⟨ ⟦⟧-cong (proj₁ (IsMonoid.identity (Monoid.isMonoid F.monoid)) F.ε) ⟩
    ⟦ F.ε ⟧ ∎)
    where
      open GroupP To
      open EqR T.setoid
  ⁻¹-homo : Homomorphic₁ ⟦_⟧ F._⁻¹ T._⁻¹
  ⁻¹-homo x = left-inverse-unique ⟦ F._⁻¹ x ⟧ ⟦ x ⟧ (begin
    T._∙_  ⟦ F._⁻¹ x ⟧ ⟦ x ⟧ ≈⟨ T.sym (∙-homo (F._⁻¹ x) x) ⟩
    ⟦ F._∙_ (F._⁻¹ x) x ⟧   ≈⟨ ⟦⟧-cong (proj₁ (IsGroup.inverse F.isGroup) x) ⟩ 
    ⟦ F.ε ⟧               ≈⟨ ε-homo ⟩
    T.ε                  ∎)
    where
      open GroupP To
      open EqR T.setoid

_⟪_⟫ : ∀{c ℓ c′ ℓ′} {G : Group c ℓ} {F : Group c′ ℓ′} → (M : G -Group⟶ F) → Group.Carrier G → Group.Carrier F
f ⟪ x ⟫ = _-Group⟶_.⟦_⟧ f x

GrpId : ∀{c ℓ} {G : Group c ℓ} → G -Group⟶ G
GrpId {G = G} = record { ⟦_⟧ = ⟦_⟧ ; ⟦⟧-cong = ⟦⟧-cong ; ∙-homo = ∙-homo }
  where
    open Algebra.Group G
    open Definitions Carrier Carrier _≈_
    ⟦_⟧ : Carrier → Carrier
    ⟦_⟧ = λ x → x
    ⟦⟧-cong : ⟦_⟧ Preserves _≈_ ⟶ _≈_
    ⟦⟧-cong = λ x → x
    ∙-homo : Homomorphic₂ ⟦_⟧ _∙_ _∙_
    ∙-homo x y = IsEquivalence.refl (Setoid.isEquivalence setoid)

_∘_ : ∀{c₁ ℓ₁ c₂ ℓ₂ c₃ ℓ₃} {G₁ : Group c₁ ℓ₁} {G₂ : Group c₂ ℓ₂} {G₃ : Group c₃ ℓ₃}
  → (g : G₂ -Group⟶ G₃) → (f : G₁ -Group⟶ G₂) → G₁ -Group⟶ G₃
_∘_ {G₁ = G₁} {G₂} {G₃} g f = record { ⟦_⟧ = ⟦_⟧ ; ⟦⟧-cong = ⟦⟧-cong ; ∙-homo = ∙-homo }
  where
    module F = Group G₁
    module M = Group G₂
    module T = Group G₃
    module hom = _-Group⟶_
    open Definitions (F.Carrier) (T.Carrier) (T._≈_)
    ⟦_⟧ : F.Carrier → T.Carrier
    ⟦ x ⟧ = g ⟪ f ⟪ x ⟫ ⟫
    ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
    ⟦⟧-cong x = hom.⟦⟧-cong g (hom.⟦⟧-cong f x)
    ∙-homo : Homomorphic₂ ⟦_⟧ (F._∙_) (T._∙_)
    ∙-homo x y = begin
      ⟦ F._∙_ x y ⟧                     ≈⟨ hom.⟦⟧-cong g (hom.∙-homo f x y) ⟩
      g ⟪ M._∙_ (f ⟪ x ⟫) (f ⟪ y ⟫) ⟫   ≈⟨ hom.∙-homo g (f ⟪ x ⟫) (f ⟪ y ⟫) ⟩
      T._∙_ ⟦ x ⟧ ⟦ y ⟧ ∎
      where
        open IsEquivalence T.isEquivalence
        open EqR T.setoid

_≈_ : ∀{c ℓ c′ ℓ′} {G₁ : Group c ℓ} {G₂ : Group c′ ℓ′} → Rel (G₁ -Group⟶ G₂) (ℓ′ ⊔ c)
_≈_ {G₁ = G₁} {G₂} φ ψ = ∀(x : F.Carrier) → T._≈_ (φ ⟪ x ⟫) (ψ ⟪ x ⟫)
  where
    module F = Group G₁
    module T = Group G₂

≈-refl : ∀{c ℓ c′ ℓ′} {G₁ : Group c ℓ} {G₂ : Group c′ ℓ′} {F : G₁ -Group⟶ G₂} → F ≈ F
≈-refl {G₁ = G₁} {F = F} _ = _-Group⟶_.⟦⟧-cong F (IsEquivalence.refl (Group.isEquivalence G₁))

≈-sym : ∀{c ℓ c′ ℓ′} {G₁ : Group c ℓ} {G₂ : Group c′ ℓ′} {F G : G₁ -Group⟶ G₂} → F ≈ G → G ≈ F
≈-sym {G₁ = G₁} {G₂} {F} {G} F≈G x = IsEquivalence.sym (Group.isEquivalence G₂)(F≈G x)

≈-trans : ∀{c ℓ c′ ℓ′} {G₁ : Group c ℓ} {G₂ : Group c′ ℓ′} {F G H : G₁ -Group⟶ G₂}
        → F ≈ G → G ≈ H → F ≈ H
≈-trans {G₁ = G₁} {G₂} {F} {G} F≈G G≈H x = IsEquivalence.trans (Group.isEquivalence G₂) (F≈G x) (G≈H x)

Grp : ∀{c ℓ} → Category _ _ _
Grp {c} {ℓ} = record { Obj = Group c ℓ
                     ; Hom = _-Group⟶_
                     ; Id = GrpId
                     ; _o_ = _∘_
                     ; _≈_ = _≈_
                     ; isCategory = isCategory
                     }
  where
    isCategory : IsCategory (Group c ℓ) _-Group⟶_ _≈_ _∘_ GrpId
    isCategory =
      record { isEquivalence = record { refl  = λ {F} → ≈-refl {F = F}
                                      ; sym   = λ {F} {G} → ≈-sym {F = F} {G}
                                      ; trans = λ {F} {G} {H} → ≈-trans {F = F} {G} {H}
                                      }
             ; identityL   = λ {G₁} {G₂} {f} → identityL {G₁} {G₂} {f}
             ; identityR   = λ {G₁} {G₂} {f} → identityR {G₁} {G₂} {f}
             ; o-resp-≈    = λ {A} {B} {C} {f} {g} {h} {i} → o-resp-≈ {A} {B} {C} {f} {g} {h} {i}
             ; associative = λ {G₁} {G₂} {G₃} {G₄} {f} {g} {h} → associative {G₁} {G₂} {G₃} {G₄} {f} {g} {h}
             }
      where
        identityL : {G₁ G₂ : Group c ℓ} {f : G₁ -Group⟶ G₂} → (GrpId ∘ f) ≈ f
        identityL {G₁} {G₂} {f} = ≈-refl {G₁ = G₁} {F = f}
        identityR : {G₁ G₂ : Group c ℓ} {f : G₁ -Group⟶ G₂} → (f ∘ GrpId) ≈ f
        identityR {G₁} {G₂} {f} = ≈-refl {G₁ = G₁} {F = f}
        o-resp-≈ : {G₁ G₂ G₃ : Group c ℓ} {f g : G₁ -Group⟶ G₂} {h i : G₂ -Group⟶ G₃}
                 → f ≈ g → h ≈ i → (h ∘ f) ≈ (i ∘ g)
        o-resp-≈ {G₁} {G₂} {G₃} {f} {g} {h} {i} f≈g h≈i x = begin
            (h ⟪ f ⟪ x ⟫ ⟫)           ≈⟨ (h≈i ( f ⟪ x ⟫ )) ⟩
            (i ⟪ f ⟪ x ⟫ ⟫)           ≈⟨ _-Group⟶_.⟦⟧-cong i (f≈g x) ⟩
            (i ⟪ g ⟪ x ⟫ ⟫)           ∎
          where
            module F = Group G₁
            module M = Group G₂
            module T = Group G₃
            open IsEquivalence T.isEquivalence
            open EqR T.setoid
        associative : {G₁ G₂ G₃ G₄ : Group c ℓ} {f : G₃ -Group⟶ G₄} {g : G₂ -Group⟶ G₃} {h : G₁ -Group⟶ G₂}
                    → (f ∘ (g ∘ h)) ≈ ((f ∘ g) ∘ h)
        associative {G₁} {G₂} {G₃} {G₄} {f} {g} {h} = ≈-refl {G₁ = G₁} {F = f ∘ (g ∘ h)}

