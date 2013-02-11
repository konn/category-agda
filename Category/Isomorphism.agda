{-# OPTIONS --universe-polymorphism #-}
import Category

module Category.Isomorphism {c₁ c₂ ℓ} (C : Category.Category c₁ c₂ ℓ) where
open Category.Category C
open import Level
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary
open import Relation.Binary.Core

record _⁻¹≈_ {A B} (f : Hom A B) (g : Hom B A) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  field
    invˡ : g o f ≈ Id
    invʳ : f o g ≈ Id

record Iso {A B : Obj} (f : Hom A B) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  field
    inverse : Hom B A
    proof : f ⁻¹≈ inverse

record _≅_ (A : Obj)  (B : Obj) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
  field
    f : Hom A B
    iso : Iso f

inverse-unique : {A B : Obj} {f : Hom A B} {g g′ : Hom B A} → f ⁻¹≈ g → f ⁻¹≈ g′ → g ≈ g′
inverse-unique {f = f} {g} {g′} g-inv g′-inv =
  begin
    g             ≈⟨ ≈-sym₂ identityL ⟩
    Id o g        ≈⟨ o-resp-≈ ≈-refl (≈-sym₁ (_⁻¹≈_.invˡ g′-inv)) ⟩
    (g′ o f) o g   ≈⟨ ≈-sym₂ associative ⟩
    g′ o (f o g)   ≈⟨ o-resp-≈ (_⁻¹≈_.invʳ g-inv) ≈-refl ⟩
    g′ o Id        ≈⟨ identityR ⟩
    g′
  ∎
  where
    open EqR homsetoid
    open Category.IsCategory isCategory
    open IsEquivalence isEquivalence
      renaming (refl to ≈-refl; sym to ≈-sym₂)
    open IsEquivalence isEquivalence
      renaming (sym to ≈-sym₁)

inverse-opposite : {A B : Obj} {f : Hom A B} {g : Hom B A} → f ⁻¹≈ g → g ⁻¹≈ f
inverse-opposite iso = record { invʳ = _⁻¹≈_.invˡ iso ; invˡ = _⁻¹≈_.invʳ iso }

idIso : {A : Obj} → Iso (Id {A})
idIso {A} = record { inverse = Id {A} ; proof = myProof}
  where
    open Category.IsCategory isCategory
    myProof : Id {A} ⁻¹≈ Id {A}
    myProof = record { invˡ = identityL
                     ; invʳ = identityL
                     }

≅-refl : {A : Obj} → A ≅ A
≅-refl {A} = record {f = Id ; iso = idIso }

≅-trans : {A B C : Obj} → A ≅ B → B ≅ C → A ≅ C
≅-trans {A} {B} {C} A≅B B≅C = record { f = g o h
                                      ; iso = iso
                                      }
  where
    module ACongB = _≅_ A≅B
    module BCongC = _≅_ B≅C
    g = BCongC.f
    h = ACongB.f
    module IsoG = Iso BCongC.iso
    module IsoH = Iso ACongB.iso
    g⁻¹ = IsoG.inverse
    h⁻¹ = IsoH.inverse
    module ProofH = _⁻¹≈_ IsoH.proof
    module ProofG = _⁻¹≈_ IsoG.proof
    invˡ : (h⁻¹ o g⁻¹) o (g o h) ≈ Id
    invˡ = begin
             (h⁻¹ o g⁻¹) o (g o h)  ≈⟨ associative ⟩
             ((h⁻¹ o g⁻¹) o g) o h  ≈⟨ o-resp-≈ ≈-refl (≈-sym′ associative) ⟩
             (h⁻¹ o (g⁻¹ o g)) o h  ≈⟨ o-resp-≈ ≈-refl (o-resp-≈ (ProofG.invˡ) ≈-refl′) ⟩
             (h⁻¹ o Id) o h        ≈⟨ o-resp-≈ ≈-refl identityR ⟩
             h⁻¹ o h               ≈⟨ ProofH.invˡ ⟩
             Id
          ∎
      where
        open EqR homsetoid
        open Category.IsCategory isCategory
        open IsEquivalence isEquivalence
          renaming (refl to ≈-refl; sym to ≈-sym)
        open IsEquivalence isEquivalence
          renaming (refl to ≈-refl′; sym to ≈-sym′)
    invʳ : (g o h) o (h⁻¹ o g⁻¹)  ≈ Id
    invʳ = begin
             (g o h) o (h⁻¹ o g⁻¹)  ≈⟨ associative ⟩
             ((g o h) o h⁻¹) o g⁻¹  ≈⟨ o-resp-≈ ≈-refl (≈-sym′ associative) ⟩
             (g o (h o h⁻¹)) o g⁻¹  ≈⟨ o-resp-≈ ≈-refl (o-resp-≈ (ProofH.invʳ) ≈-refl′) ⟩
             (g o Id) o g⁻¹        ≈⟨ o-resp-≈ ≈-refl identityR ⟩
             g o g⁻¹               ≈⟨ ProofG.invʳ ⟩
             Id
          ∎
      where
        open EqR homsetoid
        open Category.IsCategory isCategory
        open IsEquivalence isEquivalence
          renaming (refl to ≈-refl; sym to ≈-sym)
        open IsEquivalence isEquivalence
          renaming (refl to ≈-refl′; sym to ≈-sym′)

    proof : (g o h) ⁻¹≈ (h⁻¹ o g⁻¹)
    proof = record { invˡ = invˡ ; invʳ = invʳ }
    iso : Iso (g o h)
    iso = record { inverse = h⁻¹ o g⁻¹
                 ; proof = proof
                 }

≅-sym : {A B : Obj} → A ≅ B → B ≅ A
≅-sym {A} {B} A≅B = record { f = inverse ; iso = iso }
  where
    module ACongB = _≅_ A≅B
    module IsoF = Iso ACongB.iso
    inverse = IsoF.inverse
    iso = record { inverse = ACongB.f ; proof = inverse-opposite IsoF.proof }

≅-is-equivalence : IsEquivalence _≅_
≅-is-equivalence = record { refl  = ≅-refl
                          ; sym   = ≅-sym
                          ; trans = ≅-trans
                          }


