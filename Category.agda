{-# OPTIONS --universe-polymorphism #-}
module Category where
open import Level
open import Function
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
    o-resp-≈ : {A B C : Obj} {f g : Hom A B} {h i : Hom B C} → f ≈ g → h ≈ i → (h o f) ≈ (i o g)
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

  op : Category c₁ c₂ ℓ
  op = record { Obj = Obj ; Hom = flip Hom ; _o_ = flip _o_ ; _≈_ = _≈_ ; Id = Id ; isCategory = opIsCategory }
    where
      opIsCategory : IsCategory {c₁} {c₂} {ℓ} Obj (flip Hom) _≈_ (flip _o_) Id 
      opIsCategory = record { isEquivalence = IsCategory.isEquivalence isCategory
                            ; identityL = IsCategory.identityR isCategory
                            ; identityR = IsCategory.identityL isCategory
                            ; associative = (IsEquivalence.sym (IsCategory.isEquivalence isCategory)) (IsCategory.associative isCategory)
                            ; o-resp-≈ = flip (IsCategory.o-resp-≈ isCategory)
                            }
  dom : {A B : Obj} → Hom A B → Obj
  dom {A} _ = A
  cod : {A B : Obj} → Hom A B → Obj
  cod {B = B} _ = B
  homsetoid : {A B : Obj } → Setoid c₂ ℓ
  homsetoid {A} {B} = record { Carrier = Hom A B
                             ; isEquivalence = IsCategory.isEquivalence isCategory
                             }

Obj : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → Set c₁
Obj  C = Category.Obj C

Hom : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → Obj C → Obj C → Set c₂
Hom C = Category.Hom C

_[_≈_] : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {A B : Obj C} → Rel (Hom C A B) ℓ
C [ f ≈ g ] = Category._≈_ C f g

_[_o_] : ∀{c₁ c₂ ℓ} → (C : Category c₁ c₂ ℓ) → {a b c : Obj C} → Hom C b c → Hom C a b → Hom C a c
C [ f o g ] = Category._o_ C f g

infixr 9 _[_o_]
infix  4 _[_≈_]

Id : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → (A : Obj C) →  Hom C A A
Id {C = C} A = Category.Id C {A}

record IsFunctor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (C : Category c₁ c₂ ℓ) (D : Category c₁′ c₂′ ℓ′)
                 (FObj : Obj C → Obj D)
                 (FMap : {A B : Obj C} → Hom C A B → Hom D (FObj A) (FObj B))
                 : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    ≈-cong : {A B : Obj C} {f g : Hom C A B} → C [ f ≈ g ] → D [ FMap f ≈ FMap g ]
    identity : {A : Obj C} →  D [ (FMap {A} {A} (Id {_} {_} {_} {C} A)) ≈ (Id {_} {_} {_} {D} (FObj A)) ]
    distr : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
      → D [ FMap (C [ g o f ]) ≈ (D [ FMap g o FMap f ] )]

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
