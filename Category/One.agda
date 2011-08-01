module Category.One where
open import Category
open import Level
open import Relation.Binary
open import Relation.Binary.Core

data OneObject : Set where
  OneObj : OneObject

data OneMor : OneObject → OneObject → Set where
  OneIdMor : OneMor OneObj OneObj

comp : {A B C : OneObject} → OneMor B C → OneMor A B → OneMor A C 
comp OneIdMor OneIdMor = OneIdMor

≡-symm : {A B : OneObject} → Symmetric {zero} {zero} {OneMor A B} _≡_
≡-symm refl = refl

≡-trans : {A B : OneObject} → Transitive {zero} {zero} {OneMor A B} _≡_
≡-trans refl refl = refl

OneEquiv : {A B : OneObject} → IsEquivalence {zero} {zero} {OneMor A B} _≡_
OneEquiv = record { refl = refl  ; sym = ≡-symm; trans = ≡-trans}

OneID : {A : OneObject} → OneMor A A
OneID {OneObj} = OneIdMor

OneAssoc : {A B C D : OneObject} {f : OneMor C D} {g : OneMor B C } {h : OneMor A B}
           → comp f (comp g h) ≡ comp (comp f g) h 
OneAssoc {OneObj} {OneObj} {OneObj} {OneObj} {OneIdMor} {OneIdMor} {OneIdMor} = refl

OneIdentityL : {A B : OneObject} {f : OneMor A B} → (comp OneID f) ≡ f
OneIdentityL {OneObj} {OneObj} {OneIdMor} = refl 

OneIdentityR : {A B : OneObject} {f : OneMor A B} → (comp f OneID) ≡ f
OneIdentityR {OneObj} {OneObj} {OneIdMor} = refl 


isCategory : IsCategory {zero} {zero} {zero} OneObject OneMor _≡_ comp OneID
isCategory = record { isEquivalence = OneEquiv
                    ; identityL = OneIdentityL
                    ; identityR = OneIdentityR
                    ; associative = OneAssoc
                    }

ONE : Category zero zero zero
ONE = record { Obj = OneObject
             ; Hom = OneMor
             ; _≈_ = _≡_ 
             ; Id  = OneID
             ; isCategory = isCategory
             }
