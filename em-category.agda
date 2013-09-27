-- -- -- -- -- -- -- -- 
--  Monad to Eilenberg-Moore  Category
--  defines U^T and F^T as a resolution of Monad
--  checks Adjointness
-- 
--   Shinji KONO <kono@ie.u-ryukyu.ac.jp>
-- -- -- -- -- -- -- -- 

-- Monad
-- Category A
-- A = Category
-- Functor T : A → A
--T(a) = t(a)
--T(f) = tf(f)

open import Category -- https://github.com/konn/category-agda
open import Level
--open import Category.HomReasoning
open import HomReasoning
open import cat-utility
open import Category.Cat

module em-category { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ }
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { M : Monad A T η μ } where

--
--  Hom in Eilenberg-Moore Category
--
open Functor
open NTrans

record IsAlgebra {a : Obj A} { phi : Hom A (FObj T a) a } : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
   field
       identity : A [ A [ phi  o TMap η a ] ≈ id1 A a ]
       eval     : A [ A [ phi  o TMap μ a ] ≈ A [ phi o FMap T phi ] ]

record EMObj : Set (c₁ ⊔ c₂ ⊔ ℓ)  where
   field
       a         : Obj A
       phi       : Hom A (FObj T a) a
       isAlgebra : IsAlgebra {a} {phi}
   obj : Obj A
   obj = a
   φ : Hom A (FObj T a) a
   φ = phi
open EMObj

record Eilenberg-Moore-Hom (a : EMObj ) (b : EMObj ) : Set (c₁ ⊔ c₂ ⊔ ℓ) where
   field
       EMap    : Hom A (obj a) (obj b)
       homomorphism : A [ A [ (φ b)  o FMap T EMap ]  ≈ A [ EMap  o (φ a) ] ]
open Eilenberg-Moore-Hom

EMHom : (a : EMObj ) (b : EMObj ) -> Set (c₁ ⊔ c₂ ⊔ ℓ)
EMHom = \a b -> Eilenberg-Moore-Hom a b

Lemma-EM1 : {x : Obj A} {φ : Hom A (FObj T x) x} (a : EMObj )
               -> A [ A [ φ  o FMap T (id1 A x) ]  ≈ A [ (id1 A x) o φ ] ]
Lemma-EM1 {x} {φ} a = let open ≈-Reasoning (A) in
   begin
       φ o FMap T (id1 A x)
   ≈⟨ cdr ( IsFunctor.identity (isFunctor T) ) ⟩
       φ o (id1 A (FObj T x))
   ≈⟨ idR ⟩
       φ 
   ≈⟨ sym idL ⟩
       (id1 A x)  o φ
   ∎

EM-id : { a : EMObj } -> EMHom a a
EM-id {a} = record { EMap = id1 A (obj a);
     homomorphism = Lemma-EM1 {obj a} {phi a} a } 

open import Relation.Binary.Core

Lemma-EM2 : (a : EMObj ) 
            (b : EMObj ) 
            (c : EMObj ) 
            (g : EMHom b c)
            (f : EMHom a b)
                 -> A [ A [ φ c  o FMap T (A [ (EMap g)  o  (EMap f) ] ) ]  
                      ≈ A [ (A [ (EMap g)  o  (EMap f) ])  o φ a ] ]
Lemma-EM2 a b c g f = let 
      open ≈-Reasoning (A) in
   begin
        φ c  o FMap T ((EMap g)  o  (EMap f))
   ≈⟨ cdr (distr T) ⟩
        φ c o ( FMap T (EMap g)  o  FMap T (EMap f) )
   ≈⟨ assoc ⟩
        ( φ c o FMap T (EMap g))  o  FMap T (EMap f) 
   ≈⟨ car (homomorphism (g)) ⟩
        ( EMap g o φ b) o  FMap T (EMap f) 
   ≈⟨ sym assoc ⟩
        EMap g  o (φ b o  FMap T (EMap f) )
   ≈⟨ cdr (homomorphism (f)) ⟩
        EMap g  o (EMap f  o  φ a)
   ≈⟨ assoc ⟩
        ( (EMap g)  o  (EMap f) )  o φ a
   ∎

_∙_ :  {a b c : EMObj } -> EMHom b c -> EMHom a b -> EMHom a c
_∙_ {a} {b} {c} g f = record { EMap = A [ EMap g  o EMap f ] ; homomorphism = Lemma-EM2 a b c g f } 

_≗_ : {a : EMObj } {b : EMObj } (f g : EMHom a b ) -> Set ℓ 
_≗_ f g = A [ EMap f ≈ EMap g ]

--
-- cannot use as identityL = EMidL
--
EMidL : {C D : EMObj} -> {f : EMHom C D} → (EM-id  ∙ f) ≗ f
EMidL {C} {D} {f} = let open ≈-Reasoning (A) in idL {obj D} 
EMidR : {C D : EMObj} -> {f : EMHom C D} → (f ∙ EM-id)  ≗ f
EMidR {C} {_} {_} = let open ≈-Reasoning (A) in  idR {obj C}
EMo-resp :  {a b c : EMObj} -> {f g : EMHom a b } → {h i : EMHom  b c } → 
                          f ≗ g → h ≗ i → (h ∙ f) ≗ (i ∙ g)
EMo-resp {a} {b} {c} {f} {g} {h} {i} = ( IsCategory.o-resp-≈ (Category.isCategory A) )
EMassoc :   {a b c d : EMObj} -> {f : EMHom c d } → {g : EMHom b c } → {h : EMHom a b } →
                          (f ∙ (g ∙ h)) ≗ ((f ∙ g) ∙ h)
EMassoc {_} {_} {_} {_} {f} {g} {h} =   ( IsCategory.associative (Category.isCategory A) )

isEilenberg-MooreCategory : IsCategory EMObj EMHom _≗_ _∙_  EM-id 
isEilenberg-MooreCategory  = record  { isEquivalence =  isEquivalence 
                    ; identityL =   IsCategory.identityL (Category.isCategory A)
                    ; identityR =   IsCategory.identityR (Category.isCategory A)
                    ; o-resp-≈ =    IsCategory.o-resp-≈ (Category.isCategory A)
                    ; associative = IsCategory.associative (Category.isCategory A)
                    }
     where
         open ≈-Reasoning (A) 
         isEquivalence : {a : EMObj } {b : EMObj } ->
               IsEquivalence {_} {_} {EMHom a b } _≗_
         isEquivalence {C} {D} =      -- this is the same function as A's equivalence but has different types
           record { refl  = refl-hom
             ; sym   = sym
             ; trans = trans-hom
             } 
Eilenberg-MooreCategory : Category (c₁ ⊔ c₂ ⊔ ℓ) (c₁ ⊔ c₂ ⊔ ℓ) ℓ
Eilenberg-MooreCategory =
  record { Obj = EMObj
         ; Hom = EMHom
         ; _o_ = _∙_ 
         ; _≈_ = _≗_
         ; Id  =  EM-id 
         ; isCategory = isEilenberg-MooreCategory
          }


-- Resolution
--   T = U^T U^F
--     ε^t
--     η^T

U^T : Functor Eilenberg-MooreCategory A
U^T = record {
            FObj = \a -> obj a
          ; FMap = \f -> EMap f
        ; isFunctor = record
        {      ≈-cong   = \eq -> eq
             ; identity = refl-hom
             ; distr    = refl-hom
        }
     } where open ≈-Reasoning (A) 

open Monad
Lemma-EM4 : (x : Obj A ) -> A [ A [ TMap μ x  o TMap η (FObj T x) ] ≈ id1 A (FObj T x) ]
Lemma-EM4 x = let  open ≈-Reasoning (A) in
    begin
       TMap μ x  o TMap η (FObj T x) 
    ≈⟨ IsMonad.unity1 (isMonad M) ⟩
       id1 A (FObj T x)
    ∎

Lemma-EM5 : (x : Obj A ) -> A [ A [ ( TMap μ x)  o TMap μ (FObj T x) ] ≈ A [ ( TMap μ x) o FMap T ( TMap μ x) ] ]
Lemma-EM5 x =  let  open ≈-Reasoning (A) in
    begin
       ( TMap μ x)  o TMap μ (FObj T x) 
    ≈⟨ IsMonad.assoc (isMonad M) ⟩
       ( TMap μ x) o FMap T ( TMap μ x)
    ∎

ftobj : Obj A -> EMObj
ftobj = \x -> record { a = FObj T x ; phi = TMap μ x; 
 isAlgebra = record {
      identity = Lemma-EM4 x;
      eval     = Lemma-EM5 x
 } }

Lemma-EM6 :  (a b : Obj A ) -> (f : Hom A a b ) ->
      A [ A [ (φ (ftobj b))  o FMap T (FMap T f) ]  ≈ A [ FMap T f  o (φ (ftobj a)) ] ]
Lemma-EM6 a b f =  let  open ≈-Reasoning (A) in
    begin
       (φ (ftobj b))  o FMap T (FMap T f)
    ≈⟨⟩
       TMap μ b  o FMap T (FMap T f)
    ≈⟨ sym (nat μ) ⟩
       FMap T f  o TMap μ a
    ≈⟨⟩
       FMap T f  o (φ (ftobj a))
    ∎

ftmap : {a b : Obj A} -> (Hom A a b) -> EMHom (ftobj a) (ftobj b)
ftmap {a} {b} f = record { EMap = FMap T f; homomorphism =  Lemma-EM6 a b f }

F^T : Functor A Eilenberg-MooreCategory
F^T = record {
        FObj = ftobj
        ; FMap = ftmap
        ; isFunctor = record {
               ≈-cong   = ≈-cong   
             ; identity = identity 
             ; distr    = distr1 
        }
     } where 
        ≈-cong   : {a b : Obj A} {f g : Hom A a b} → A [ f ≈ g ] → (ftmap f) ≗ (ftmap g)
        ≈-cong   = let  open ≈-Reasoning (A) in ( fcong T )
        identity :  {a : Obj A} →  ftmap (id1 A a) ≗ EM-id {ftobj a}
        identity = IsFunctor.identity ( isFunctor T )
        distr1    :  {a b c : Obj A} {f : Hom A a b} {g : Hom A b c} → ftmap (A [ g o f ]) ≗ ( ftmap g ∙ ftmap f )
        distr1    =  let  open ≈-Reasoning (A) in ( distr T )

-- T = (U^T ○ F^T)    

Lemma-EM7 :  ∀{a b : Obj A} -> (f : Hom A a b ) -> A [ FMap T f  ≈ FMap (U^T ○ F^T) f ]
Lemma-EM7 {a} {b} f = let open ≈-Reasoning (A) in
     sym ( begin
          FMap (U^T ○ F^T) f
     ≈⟨⟩
          EMap ( ftmap f )
     ≈⟨⟩
           FMap T f
     ∎ )

Lemma-EM8 :  T ≃  (U^T ○ F^T)
Lemma-EM8 f = Category.Cat.refl (Lemma-EM7 f)

η^T : NTrans A A identityFunctor ( U^T ○ F^T ) 
η^T = record { TMap = \x -> TMap η x ; isNTrans = isNTrans1 } where
       commute1 :  {a b : Obj A} {f : Hom A a b}
            → A [ A [ ( FMap ( U^T ○ F^T ) f ) o  ( TMap η a ) ]  ≈ A [ (TMap η b ) o  f  ] ]
       commute1 {a} {b} {f} =  let open ≈-Reasoning (A) in
          begin
              ( FMap ( U^T ○ F^T ) f ) o  ( TMap η a )
          ≈⟨ sym (resp refl-hom (Lemma-EM7 f)) ⟩
              FMap T f o TMap η a
          ≈⟨ nat η ⟩
              TMap η b o f
          ∎
       isNTrans1 : IsNTrans A A identityFunctor ( U^T ○ F^T ) (\a -> TMap η a)
       isNTrans1 = record { commute = commute1 }

Lemma-EM9 : (a : EMObj) -> A [ A [ (φ a)  o FMap T (φ a) ]  ≈ A [ (φ a)  o (φ (FObj ( F^T ○ U^T ) a)) ] ]
Lemma-EM9 a = let open ≈-Reasoning (A) in
          sym ( begin
              (φ a)  o (φ (FObj ( F^T ○ U^T ) a))
          ≈⟨⟩
              (φ a)  o (TMap μ (obj a))
          ≈⟨ IsAlgebra.eval (isAlgebra a) ⟩
              (φ a)  o FMap T (φ a)
          ∎ )

emap-ε : (a : EMObj ) -> EMHom (FObj ( F^T ○ U^T ) a)  a
emap-ε a = record { EMap = φ a ; homomorphism = Lemma-EM9 a }

ε^T : NTrans Eilenberg-MooreCategory Eilenberg-MooreCategory  ( F^T ○ U^T ) identityFunctor
ε^T = record { TMap = \a -> emap-ε a; isNTrans = isNTrans1 } where
       commute1 : {a b : EMObj } {f : EMHom a b}
            →  (f ∙ ( emap-ε a ) ) ≗ (( emap-ε b ) ∙(  FMap (F^T ○ U^T) f ) )
       commute1 {a} {b} {f} =  let open ≈-Reasoning (A) in
          sym ( begin 
             EMap (( emap-ε b ) ∙ (  FMap (F^T ○ U^T) f ))
          ≈⟨⟩
             φ b  o   FMap T (EMap f)
          ≈⟨ homomorphism f ⟩
             EMap f  o φ a
          ≈⟨⟩
             EMap (f ∙ ( emap-ε a ))
          ∎  )
       isNTrans1 : IsNTrans  Eilenberg-MooreCategory Eilenberg-MooreCategory ( F^T ○ U^T ) identityFunctor (\a -> emap-ε a )
       isNTrans1 = record { commute = \{a} {b} {f} ->  (IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory A)) )  (homomorphism f ) }  -- naturity1 {a} {b} {f}
                                                                                 
--
-- μ = U^T ε U^F
--

emap-μ :  (a : Obj A) -> Hom A (FObj ( U^T ○ F^T ) (FObj ( U^T ○ F^T ) a)) (FObj ( U^T ○ F^T ) a)
emap-μ a = FMap U^T ( TMap ε^T ( FObj F^T a ))

μ^T : NTrans A A (( U^T ○ F^T ) ○ ( U^T ○ F^T )) ( U^T ○ F^T )
μ^T = record { TMap = emap-μ ; isNTrans = isNTrans1 } where
        commute1 : {a b : Obj A} {f : Hom A a b}
             →  A [ A [ (FMap (U^T ○ F^T) f) o  ( emap-μ a) ]  ≈ A [ ( emap-μ b ) o  FMap (U^T ○ F^T) ( FMap (U^T ○ F^T) f)  ] ]
        commute1 {a} {b} {f} =  let open ≈-Reasoning (A) in
          sym ( begin 
             ( emap-μ b ) o  FMap (U^T ○ F^T) ( FMap (U^T ○ F^T) f) 
          ≈⟨⟩
             (FMap U^T ( TMap ε^T ( FObj F^T b ))) o  (FMap (U^T ○ F^T) ( FMap (U^T ○ F^T) f) )
          ≈⟨⟩
             (TMap μ b) o (FMap T (FMap T f))
          ≈⟨ sym (nat μ) ⟩
              FMap T f  o ( TMap μ a )
          ≈⟨⟩
             (FMap (U^T ○ F^T) f) o  ( emap-μ a)
          ∎  )
        isNTrans1 : IsNTrans A A (( U^T ○ F^T ) ○ ( U^T ○ F^T )) ( U^T ○ F^T ) emap-μ
        isNTrans1 = record { commute = commute1 }

Lemma-EM10 : {x : Obj A } -> A [ TMap μ^T x ≈ FMap U^T ( TMap ε^T ( FObj F^T x ) ) ]
Lemma-EM10 {x} = let open ≈-Reasoning (A) in
          sym ( begin
              FMap U^T ( TMap ε^T ( FObj F^T x ) )
          ≈⟨⟩
              emap-μ x
          ≈⟨⟩
              TMap μ^T x
          ∎ )

Lemma-EM11 : {x : Obj A } -> A [ TMap μ x ≈ FMap U^T ( TMap ε^T ( FObj F^T x ) ) ]
Lemma-EM11 {x} = let open ≈-Reasoning (A) in
          sym ( begin
              FMap U^T ( TMap ε^T ( FObj F^T x ) )
          ≈⟨⟩
              TMap μ x
          ∎ )

Adj^T : Adjunction A Eilenberg-MooreCategory U^T F^T η^T ε^T
Adj^T = record {
           isAdjunction = record {
               adjoint1 = \{b} -> IsAlgebra.identity (isAlgebra b) ; -- adjoint1
               adjoint2 = adjoint2
           }
       } where
           adjoint1 :   { b : EMObj } →
                     A [ A [ ( FMap U^T ( TMap ε^T b))  o ( TMap η^T ( FObj U^T b )) ]  ≈ id1 A (FObj U^T b) ]
           adjoint1 {b} =  let open ≈-Reasoning (A) in
               begin
                  ( FMap U^T ( TMap ε^T b))  o ( TMap η^T ( FObj U^T b ))
               ≈⟨⟩ 
                   φ b  o TMap η (obj b)
               ≈⟨ IsAlgebra.identity (isAlgebra b) ⟩
                   id1 A (a b)
               ≈⟨⟩ 
                   id1 A (FObj U^T b)
               ∎
           adjoint2 :   {a : Obj A} →
                     Eilenberg-MooreCategory [ Eilenberg-MooreCategory [ ( TMap ε^T ( FObj F^T a ))  o ( FMap F^T ( TMap η^T a )) ]
                                     ≈ id1 Eilenberg-MooreCategory (FObj F^T a) ]
           adjoint2 {a} =  let open ≈-Reasoning (A) in
               begin
                  EMap (( TMap ε^T ( FObj F^T a )) ∙ ( FMap F^T ( TMap η^T a )) )
               ≈⟨⟩
                  TMap μ a  o FMap T ( TMap η a )
               ≈⟨ IsMonad.unity2 (isMonad M) ⟩
                  EMap (id1 Eilenberg-MooreCategory (FObj F^T a))
               ∎

open MResolution

Resolution^T : MResolution A Eilenberg-MooreCategory T U^T F^T {η^T} {ε^T} {μ^T} Adj^T 
Resolution^T = record {
     T=UF = Lemma-EM8;
     μ=UεF  = Lemma-EM11
 }


-- end
