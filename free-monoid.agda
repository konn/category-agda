-- Free Monoid and it's Universal Mapping 
---- using Sets and forgetful functor

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
module free-monoid { c c₁ c₂ ℓ : Level }   where

open import Category.Sets
open import Category.Cat
open import HomReasoning
open import cat-utility
open import Relation.Binary.Core
open import  Relation.Binary.PropositionalEquality
open import universal-mapping 

-- from https://github.com/danr/Agda-projects/blob/master/Category-Theory/FreeMonoid.agda

infixr 40 _::_
data  List  (A : Set c ) : Set c where
   [] : List A
   _::_ : A → List A → List A


infixl 30 _++_
_++_ :   {A : Set c } → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

≡-cong = Relation.Binary.PropositionalEquality.cong 

list-id-l : { A : Set c } → { x : List A } →  [] ++ x ≡ x
list-id-l {_} {_} = refl
list-id-r : { A : Set c } → { x : List A } →  x ++ [] ≡ x
list-id-r {_} {[]} =   refl
list-id-r {A} {x :: xs} =  ≡-cong ( λ y → x :: y ) ( list-id-r {A} {xs} ) 
list-assoc : {A : Set c} → { xs ys zs : List A } →
      ( xs ++ ( ys ++ zs ) ) ≡ ( ( xs ++ ys ) ++ zs )
list-assoc  {_} {[]} {_} {_} = refl
list-assoc  {A} {x :: xs}  {ys} {zs} = ≡-cong  ( λ y  → x :: y ) 
         ( list-assoc {A} {xs} {ys} {zs} )
list-o-resp-≈ :  {A : Set c} →  {f g : List A } → {h i : List A } → 
                  f ≡  g → h ≡  i → (h ++ f) ≡  (i ++ g)
list-o-resp-≈  {A} refl refl = refl
list-isEquivalence : {A : Set c} → IsEquivalence {_} {_} {List A }  _≡_ 
list-isEquivalence {A} =      -- this is the same function as A's equivalence but has different types
   record { refl  = refl
     ; sym   = sym
     ; trans = trans
     } 

open import Algebra.FunctionProperties using (Op₁; Op₂)
open import Algebra.Structures
open import Data.Product


record ≡-Monoid : Set (suc c) where
  infixl 7 _∙_
  field
    Carrier  : Set c
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≡_ _∙_ ε

open ≡-Monoid

record Monomorph ( a b : ≡-Monoid )  : Set (suc c) where
  field
      morph : Carrier a → Carrier b  
      identity     :  morph (ε a)  ≡  ε b
      homo :  ∀{x y} → morph ( _∙_ a x  y ) ≡ ( _∙_ b (morph  x ) (morph  y) )

open Monomorph

_+_ : { a b c : ≡-Monoid } → Monomorph b c → Monomorph a b → Monomorph a c
_+_ {a} {b} {c} f g =  record {
      morph = λ x →  morph  f ( morph g x ) ;
      identity  = identity1 ;
      homo  = homo1 
   } where
      identity1 : morph f ( morph g (ε a) )  ≡  ε c
      -- morph f (ε b) = ε c ,  morph g (ε a) ) ≡  ε b
      -- morph f  morph g (ε a) ) ≡  morph f (ε b) = ε c
      identity1 = trans ( ≡-cong (morph f ) ( identity g ) )  ( identity f )
      homo1 :  ∀{x y} → morph f ( morph g ( _∙_ a x  y )) ≡ ( _∙_ c (morph f (morph  g x )) (morph f (morph  g y) ) )
      --  ∀{x y} → morph f ( morph g ( _∙_ a x  y )) ≡ morph f ( ( _∙_ c  (morph  g x )) (morph  g y) ) 
      --  ∀{x y} → morph f ( ( _∙_ c  (morph  g x )) (morph  g y) )  
      --         ≡ ( _∙_ c (morph f (morph  g x )) (morph f (morph  g y) ) )
      homo1 = trans  (≡-cong (morph f ) ( homo g) ) ( homo f ) 

M-id : { a : ≡-Monoid } → Monomorph a a 
M-id = record { morph = λ x → x  ; identity = refl ; homo = refl }

_==_ : { a b : ≡-Monoid } → Monomorph a b → Monomorph a b → Set c 
_==_  f g =  morph f ≡ morph g

isMonoids : IsCategory ≡-Monoid Monomorph _==_  _+_  (M-id)
isMonoids  = record  { isEquivalence =  isEquivalence1 
                    ; identityL =  refl
                    ; identityR =  refl
                    ; associative = refl
                    ; o-resp-≈ =    λ {a} {b} {c} {f} {g} {h} {i} → o-resp-≈ {a} {b} {c} {f} {g} {h} {i}
                    }
     where
        o-resp-≈ :  {a b c :  ≡-Monoid } {f g : Monomorph a b } → {h i : Monomorph b c } → 
                          f ==  g → h ==  i → (h + f) ==  (i + g)
        o-resp-≈  {A} refl refl = refl
        isEquivalence1 : { a b : ≡-Monoid } → IsEquivalence {_} {_} {Monomorph a b}  _==_ 
        isEquivalence1  =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl
             ; sym   = sym
             ; trans = trans
             } 
Monoids : Category _ _ _
Monoids  =
  record { Obj =  ≡-Monoid 
         ; Hom = Monomorph
         ; _o_ = _+_  
         ; _≈_ = _==_
         ; Id  =  M-id
         ; isCategory = isMonoids 
           }

A = Sets {c}
B = Monoids  

open Functor

U : Functor B A
U = record {
       FObj = λ m → Carrier m ;
       FMap = λ f → morph f ;
       isFunctor = record {
              ≈-cong   = λ x → x
             ; identity = refl
             ; distr    = refl
       }
   } 

-- FObj 
list  : (a : Set c) → ≡-Monoid
list a = record {
    Carrier    =  List a
    ; _∙_      = _++_
    ; ε        = []
    ; isMonoid = record {
          identity = ( ( λ x → list-id-l {a}  ) , ( λ x → list-id-r {a} ) ) ;
          isSemigroup = record {
               assoc =  λ x → λ y → λ z → sym ( list-assoc {a} {x} {y} {z} )
             ; isEquivalence = list-isEquivalence
             ; ∙-cong = λ x → λ y →  list-o-resp-≈ y x
          }
      }
    }

Generator : Obj A → Obj B
Generator s =  list s

-- solution

open UniversalMapping

--   [a,b,c] → f(a) ∙ f(b) ∙ f(c)
Φ :  {a : Obj A } {b : Obj B} { f : Hom A a (FObj U b) } →  List a → Carrier b
Φ {a} {b} {f} [] = ε b
Φ {a} {b} {f} ( x :: xs ) = _∙_ b  ( f x ) (Φ {a} {b} {f} xs )

solution : (a : Obj A ) (b : Obj B) ( f : Hom A a (FObj U b) ) →  Hom B (Generator a ) b 
solution a b f = record {
         morph = λ (l : List a) → Φ l   ;
         identity = refl ;
         homo = λ {x y} → homo1 x y 
    } where
        _*_ : Carrier b → Carrier b → Carrier b
        _*_  f g = _∙_ b f g
        homo1 : (x y : Carrier (Generator a)) → Φ ((Generator a ∙ x) y) ≡ (b ∙ Φ x) (Φ y)
        homo1 [] y = sym (proj₁ ( IsMonoid.identity ( isMonoid b) ) (Φ y))
        homo1 (x :: xs) y = let open ≡-Reasoning in 
             sym ( begin
                (Φ {a} {b} {f} (x :: xs)) * (Φ {a} {b} {f} y)
             ≡⟨⟩
                 ((f x) * (Φ {a} {b} {f} xs)) * (Φ {a} {b} {f} y)
             ≡⟨ ( IsMonoid.assoc ( isMonoid b )) _ _ _ ⟩
                (f x) * ( (Φ {a} {b} {f} xs)  * (Φ {a} {b} {f} y) )
             ≡⟨ sym ( (IsMonoid.∙-cong (isMonoid b)) refl (homo1 xs y )) ⟩
                (f x) * ( Φ {a} {b} {f} ( xs ++ y ) )
             ≡⟨⟩
                Φ {a} {b} {f} ( x :: ( xs ++ y ) )
             ≡⟨⟩
                Φ {a} {b} {f} ( (x ::  xs) ++ y ) 
             ≡⟨⟩
                Φ {a} {b} {f} ((Generator a ∙ x :: xs) y) 
             ∎ )

eta :  (a : Obj A) → Hom A a ( FObj U (Generator a) )
eta  a = λ ( x : a ) →  x :: []

-- Functional Extensionality Axiom (We cannot prove this in Agda / Coq, just assumming )
-- postulate extensionality : { a b : Obj A } {f g : Hom A a b } → (∀ {x} → (f x ≡ g x))  → ( f ≡ g ) 
postulate extensionality : Relation.Binary.PropositionalEquality.Extensionality c c 

FreeMonoidUniveralMapping : UniversalMapping A B U Generator eta  
FreeMonoidUniveralMapping = 
    record {
       _* = λ {a b} → λ f → solution a b f ; 
       isUniversalMapping = record {
             universalMapping = λ {a b f} → universalMapping {a} {b} {f} ; 
             uniquness = λ {a b f g} → uniquness {a} {b} {f} {g}
       }
    } where
        universalMapping :  {a : Obj A } {b : Obj B} { f : Hom A a (FObj U b) } →  FMap U ( solution a b f  ) o eta a   ≡ f
        universalMapping {a} {b} {f} = let open ≡-Reasoning in 
                     begin
                         FMap U ( solution a b f ) o eta a   
                     ≡⟨⟩
                         ( λ (x : a ) → Φ {a} {b} {f} (eta a x) )
                     ≡⟨⟩
                         ( λ (x : a ) → Φ {a} {b} {f} ( x :: [] ) )
                     ≡⟨⟩
                         ( λ (x : a ) →  _∙_ b  ( f x ) (Φ {a} {b} {f} [] ) )
                     ≡⟨⟩
                         ( λ (x : a ) →  _∙_ b  ( f x ) ( ε b ) )
                     ≡⟨ ≡-cong ( λ  g → ( ( λ (x : a ) →  g x ) )) (extensionality {a} lemma-ext1) ⟩
                         ( λ (x : a ) →  f x  )
                     ≡⟨⟩
                          f
                     ∎  where
                        lemma-ext1 : ∀( x : a ) →  _∙_ b  ( f x ) ( ε b )  ≡ f x
                        lemma-ext1 x = ( proj₂ ( IsMonoid.identity ( isMonoid b) ) ) (f x)
        uniquness :  {a : Obj A } {b : Obj B} { f : Hom A a (FObj U b) } →
             { g :  Hom B (Generator a) b } → (FMap U g) o (eta a )  ≡ f  → B [ solution a b f ≈ g ]
        uniquness {a} {b} {f} {g} eq =  
                     extensionality  lemma-ext2 where
                        lemma-ext2 : ( ∀( x : List a ) → (morph ( solution a b f)) x  ≡ (morph g) x  )
                        -- (morph ( solution a b f)) []  ≡ (morph g) []  )
                        lemma-ext2 [] = let open ≡-Reasoning in
                             begin
                                (morph ( solution a b f)) []
                             ≡⟨ identity ( solution a b f) ⟩
                                ε b
                             ≡⟨ sym ( identity g ) ⟩
                                (morph g) []
                             ∎  
                        lemma-ext2 (x :: xs)  = let open ≡-Reasoning in
                             begin
                                (morph ( solution a b f)) ( x :: xs )
                             ≡⟨ homo ( solution a b f) {x :: []} {xs} ⟩
                                 _∙_ b ((morph ( solution a b f)) ( x :: []) )  ((morph ( solution a b f)) xs )
                             ≡⟨  ≡-cong ( λ  k → (_∙_ b ((morph ( solution a b f)) ( x :: []) ) k )) (lemma-ext2 xs )   ⟩
                                 _∙_ b ((morph ( solution a b f)) ( x :: []) )  ((morph g) ( xs ))
                             ≡⟨  ≡-cong ( λ k → ( _∙_ b ( k x ) ((morph g) ( xs )) )) (
                                 begin
                                     ( λ x → (morph ( solution a b f)) ( x :: [] ) )
                                 ≡⟨ extensionality {a} lemma-ext3 ⟩
                                     ( λ x → (morph g) ( x :: [] ) )
                                 ∎  
                             ) ⟩
                                 _∙_ b ((morph g) ( x :: [] )) ((morph g) ( xs ))
                             ≡⟨ sym ( homo g ) ⟩
                                (morph g) ( x :: xs )
                             ∎   where
                         lemma-ext3 :  ∀( x : a ) → (morph ( solution a b f)) (x :: [])  ≡ (morph g) ( x :: []  )
                         lemma-ext3 x = let open ≡-Reasoning in
                             begin
                               (morph ( solution a b f)) (x :: [])
                             ≡⟨  ( proj₂  ( IsMonoid.identity ( isMonoid b) )(f x) ) ⟩
                                f x
                             ≡⟨  sym ( ≡-cong (λ f → f x )  eq  ) ⟩
                               (morph g) ( x :: []  )
                             ∎   

open NTrans
--   fm-ε b = Φ
fm-ε :  NTrans B B ( ( FunctorF A B FreeMonoidUniveralMapping) ○ U) identityFunctor
fm-ε =  nat-ε A B {U} {Generator} {eta} FreeMonoidUniveralMapping 
--  TMap fm-ε

open Adjunction

-- A = Sets {c}
-- B = Monoids  
-- U   underline funcotr
-- F   generator = x :: []
-- Eta          x :: []
-- Epsiron      morph = Φ

adj = UMAdjunction  A B  U Generator eta FreeMonoidUniveralMapping 

 


