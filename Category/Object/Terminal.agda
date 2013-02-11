{-# OPTIONS --universe-polymorphism #-}
import Category

module Category.Object.Terminal {c₁ c₂ ℓ} (C : Category.Category c₁ c₂ ℓ) where
open Category.Category C
open import Category.Isomorphism C
open import Level
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary
open import Relation.Binary.Core

record Terminal : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
  field
    ⊤ : Obj
    ! : ∀{A : Obj} → Hom A ⊤
    !-unique : ∀{A : Obj} → (f : Hom A ⊤) → (f ≈ !)

  !-unique₂ : ∀{A : Obj} → (f : Hom A ⊤) → (g : Hom A ⊤) → (f ≈ g)
  !-unique₂ f g = begin
                    f ≈⟨ !-unique f ⟩
                    ! ≈⟨ ≈-sym (!-unique g) ⟩
                    g
                 ∎
     where
       open EqR homsetoid
       open Category.IsCategory isCategory
       open IsEquivalence isEquivalence renaming (sym to ≈-sym)


open Terminal

terminal-up-to-iso : (t₁ t₂ : Terminal) → ⊤ t₁ ≅ ⊤ t₂
terminal-up-to-iso t₁ t₂ = record { f = ! t₂ {⊤ t₁} ; iso = iso }
  where
    proof = record { invˡ = !-unique₂ t₁ (! t₁ o ! t₂) Id
                   ; invʳ = !-unique₂ t₂ (! t₂ o ! t₁) Id
                   }
    iso = record { inverse = ! t₁ ; proof = proof}
