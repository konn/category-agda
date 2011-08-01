{-# OPTIONS --universe-polymorphism #-}
module Category where
open import Level
open import Relation.Binary
open import Relation.Binary.Core

record IsCategory {c₁ c₂ ℓ : Level} (Obj : Set c₁)
                  (Hom : Obj → Obj → Set c₂)
                  (_≈_ : {A B : Obj} → Rel (Hom A B) ℓ)
                  (_o_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C)
                  (Id  : {A : Obj} → Hom A A) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
  field
    isEquivalence : {A B : Obj} → IsEquivalence {c₂} {ℓ} {Hom A B} _≈_ 
    identityL : {A B : Obj} → {f : Hom A B} → (Id o f) ≈ f
    identityR : {A B : Obj} → {f : Hom A B} → (f o Id) ≈ f
    associative : {A B C D : Obj} {f : Hom C D}  {g : Hom B C} {h : Hom A B}
                                  → (f o (g o h)) ≈ ((f o g) o h)

record Category c₁ c₂ ℓ : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
  infixr 9 _o_
  infix  4 _≈_
  field
    Obj : Set c₁
    Hom : Obj → Obj → Set c₂
    _o_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C
    _≈_ : {A B : Obj} → Rel (Hom A B) ℓ
    Id  : {A : Obj} → Hom A A
    isCategory : IsCategory Obj Hom _≈_ _o_ Id

Obj : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → Set c₁
Obj {_} {_} {_} C = Category.Obj C

Hom : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → Obj C → Obj C → Set c₂
Hom C = Category.Hom C

_≈_ : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {a b : Obj C} → Rel (Hom C a b) ℓ
_≈_ {_} {_} {_} {C} = Category._≈_ C

_o_ : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} {O P Q : Obj C}
   → Hom C P Q → Hom C O P → Hom C O Q
_o_ {_} {_} {_} {C} = Category._o_ C

infixr 9 _o_
infix  4 _≈_


Id : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → (A : Obj C) →  Hom C A A
Id {_} {_} {_} {C} A = Category.Id C {A}


record IsFunctor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁′ c₂′ ℓ′)
                 (FObj : Obj C → Obj D)
                 (FMap : {A B : Obj C} → Hom C A B → Hom D (FObj A) (FObj B))
                 : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    ≈-cong : {A B : Obj C} {f g : Hom C A B} → _≈_ {_}{_}{_}{C} f g → _≈_ {_}{_}{_}{D} (FMap f) (FMap g)
    identity : {A : Obj C} → _≈_ {c₁′} {c₂′} {ℓ′} {D} (FMap (Id {c₁} {c₂} {ℓ} {C} A)) (Id {c₁′} {c₂′} {ℓ′} {D} (FObj A))
    distr : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
      → _≈_ {c₁′} {c₂′} {ℓ′} {D} (FMap {a} {c} (_o_ {_} {_} {_} {C} g f)) (_o_ {_} {_} {_} {D} (FMap g) (FMap f))

record Functor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (domain : Category c₁ c₂ ℓ) (codomain : Category c₁′ c₂′ ℓ′)
  : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    FObj : Obj domain → Obj codomain
    FMap : {A B : Obj domain} → Hom domain A B → Hom codomain (FObj A) (FObj B)
    isFunctor : IsFunctor domain codomain FObj FMap

cong : ∀{c₁ c₂} {A : Set c₁} {B : Set c₂} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong {A} {B} f refl = refl

≡-sym : ∀{c}{A : Set c} → Symmetric {_} {_} {A} _≡_
≡-sym refl = refl

≡-trans : ∀{c}{A : Set c} → Transitive {_} {_} {A} _≡_
≡-trans refl refl = refl
