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
  
  1-homo : Homomorphic₀ ⟦_⟧ F.ε T.ε
  1-homo = left-identity-unique ⟦ F.ε ⟧ ⟦ F.ε ⟧ (begin
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
    ⟦ F.ε ⟧               ≈⟨ 1-homo ⟩
    T.ε                  ∎)
    where
      open GroupP To
      open EqR T.setoid
    

GrpHom : ∀{c ℓ} → (G F : Group c ℓ) → Set (c ⊔ ℓ)
GrpHom {c} {ℓ} G F = _-Group⟶_ {c} {ℓ} {c} {ℓ} G F

GrpId : ∀{c ℓ} {G : Group c ℓ} → GrpHom G G
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
    module T = Group G₃
    module hom = _-Group⟶_
    open Definitions (F.Carrier) (T.Carrier) (T._≈_)
    ⟦_⟧ : F.Carrier → T.Carrier
    ⟦ x ⟧ = hom.⟦_⟧ g (hom.⟦_⟧ f x)
    ⟦⟧-cong : ⟦_⟧ Preserves F._≈_ ⟶ T._≈_
    ⟦⟧-cong x = hom.⟦⟧-cong g (hom.⟦⟧-cong f x)
    ∙-homo : Homomorphic₂ ⟦_⟧ (F._∙_) (T._∙_)
    ∙-homo x y = {!!}

    

{-
Grp : Category _ _ _
Grp = record { Obj = GrpObj ; Hom = GrpHom ; Id = GrpId ; isCategory = isCategory }
  where
    isCategory
-}