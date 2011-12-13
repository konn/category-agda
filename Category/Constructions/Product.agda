{-# OPTIONS --universe-polymorphism #-}
module Category.Constructions.Product where
open import Category
open import Level
open import Data.Product renaming (_×_ to _*_)
open import Relation.Binary
open import Relation.Binary.Core

_×_ : ∀{c₁ c₁′ c₂ c₂′ ℓ ℓ′} → Category c₁ c₂ ℓ → Category c₁′ c₂′ ℓ′ → Category (c₁ ⊔ c₁′) (c₂ ⊔ c₂′) (ℓ ⊔ ℓ′)
C₁ × C₂ = record { Obj = ObjProd
                 ; Hom = _⟶_
                 ; Id = IdProd
                 ; _o_ = _∘_
                 ; _≈_ = _≈_
                 ; isCategory = record { isEquivalence = record { refl  = λ {φ} → ≈-refl {φ = φ}
                                                                ; sym   = λ {φ ψ} → ≈-symm {φ = φ} {ψ}
                                                                ; trans = λ {φ ψ σ} → ≈-trans {φ = φ} {ψ} {σ}
                                                                }
                                       ; identityL = identityL
                                       ; identityR = identityR
                                       ; o-resp-≈ = o-resp-≈
                                       ; associative = associative
                                       }
                 }
  where
    ObjProd : Set _
    ObjProd = Obj C₁ * Obj C₂
    _⟶_ : ObjProd → ObjProd → Set _
    _⟶_ = λ x y → Hom C₁ (proj₁ x) (proj₁ y) * Hom C₂ (proj₂ x) (proj₂ y)
    IdProd : {A : ObjProd} → A ⟶ A
    IdProd {x} = (Id {C = C₁} (proj₁ x) , Id {C = C₂} (proj₂ x))
    _∘_ : {A B C : Obj C₁} {A′ B′ C′ : Obj C₂} → (Hom C₁ B C * Hom C₂ B′ C′) → (Hom C₁ A B * Hom C₂ A′ B′) → (Hom C₁ A C * Hom C₂ A′ C′) 
    g ∘ f = (C₁ [ proj₁ g o proj₁ f ] , C₂ [ proj₂ g o proj₂ f ] )
    _≈_ : {A B : ObjProd} → Rel (A ⟶ B) _
    φ ≈ ψ = C₁ [ proj₁ φ ≈ proj₁ ψ ] * C₂ [ proj₂ φ ≈ proj₂ ψ ]
    C₁-equiv : ∀{A B} → IsEquivalence (Category._≈_ C₁ {A = A} {B = B})
    C₁-equiv = IsCategory.isEquivalence (Category.isCategory C₁)
    C₂-equiv : ∀{A B} → IsEquivalence (Category._≈_ C₂ {A = A} {B = B})
    C₂-equiv = IsCategory.isEquivalence (Category.isCategory C₂)
    ≈-refl : {A B : ObjProd} {φ : A ⟶ B} → φ ≈ φ
    ≈-refl = (IsEquivalence.refl C₁-equiv , IsEquivalence.refl C₂-equiv)
    ≈-symm : {A B : ObjProd} {φ ψ : A ⟶ B} → φ ≈ ψ → ψ ≈ φ
    ≈-symm φ≈ψ = (IsEquivalence.sym C₁-equiv (proj₁ φ≈ψ), IsEquivalence.sym C₂-equiv (proj₂ φ≈ψ))
    ≈-trans : {A B : ObjProd} {φ ψ σ : A ⟶ B} → φ ≈ ψ → ψ ≈ σ → φ ≈ σ
    ≈-trans φ≈ψ ψ≈σ = ( IsEquivalence.trans C₁-equiv (proj₁ φ≈ψ) (proj₁ ψ≈σ)
                         , IsEquivalence.trans C₂-equiv (proj₂ φ≈ψ) (proj₂ ψ≈σ))
    identityL : {A B : ObjProd} {φ : A ⟶ B} → (IdProd ∘ φ) ≈ φ
    identityL = (IsCategory.identityL (Category.isCategory C₁), IsCategory.identityL (Category.isCategory C₂))
    identityR : {A B : ObjProd} {φ : A ⟶ B} → (φ ∘ IdProd) ≈ φ
    identityR = (IsCategory.identityR (Category.isCategory C₁), IsCategory.identityR (Category.isCategory C₂))
    o-resp-≈ : {A B C : ObjProd} {f g : A ⟶ B} {h i : B ⟶ C} → f ≈ g → h ≈ i → (h ∘ f) ≈ (i ∘ g)
    o-resp-≈ f≈g h≈i = (IsCategory.o-resp-≈ (Category.isCategory C₁) (proj₁ f≈g) (proj₁ h≈i),
                        IsCategory.o-resp-≈ (Category.isCategory C₂) (proj₂ f≈g) (proj₂ h≈i))
    associative : {A B C D : ObjProd} {f : C ⟶ D} {g : B ⟶ C} {h : A ⟶ B}
                →  (f ∘ (g ∘ h)) ≈ ((f ∘ g) ∘ h)
    associative = (IsCategory.associative (Category.isCategory C₁), IsCategory.associative (Category.isCategory C₂))
