-- -- -- -- -- -- -- -- 
--  Comparison Functor of Kelisli Category
--  defines U_K and F_K as a resolution of Monad
--  checks Adjointness
-- 
--   Shinji KONO <kono@ie.u-ryukyu.ac.jp>
-- -- -- -- -- -- -- -- 

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
--open import Category.HomReasoning                                                                                                               
open import HomReasoning
open import cat-utility
open import Category.Cat
open import Relation.Binary.Core

module comparison-functor 
      { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ }
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { M' : Monad A T η μ }
      {c₁' c₂' ℓ' : Level} ( B : Category c₁' c₂' ℓ' ) 
      { U_K : Functor B A } { F_K : Functor A B }
      { η_K : NTrans A A identityFunctor ( U_K ○ F_K ) }
      { ε_K : NTrans B B ( F_K ○ U_K ) identityFunctor } 
      { μ_K' : NTrans A A (( U_K ○ F_K ) ○ ( U_K ○ F_K )) ( U_K ○ F_K ) }
      ( AdjK : Adjunction A B U_K F_K η_K ε_K )
      ( RK : MResolution A B T U_K F_K {η_K} {ε_K} {μ_K'} AdjK )
where

open import adj-monad

T_K = U_K ○ F_K

μ_K : NTrans A A (( U_K ○ F_K ) ○ ( U_K ○ F_K )) ( U_K ○ F_K ) 
μ_K  = UεF A B U_K F_K ε_K 

M : Monad A (U_K ○ F_K ) η_K μ_K 
-- M =  Adj2Monad A B {U_K} {F_K} {η_K} {ε_K} AdjK
M =  Adj2Monad A B {U_K} {F_K} {η_K} {ε_K} AdjK

open import kleisli {c₁} {c₂} {ℓ} {A} { U_K ○ F_K } { η_K } { μ_K } { M } 

open Functor
open NTrans
open KleisliHom
open Adjunction
open MResolution

kfmap : {a b : Obj A} (f : KHom a b) -> Hom B (FObj F_K a) (FObj F_K b)
kfmap {_} {b} f = B [ TMap ε_K (FObj F_K b) o FMap F_K (KMap f) ]

K_T : Functor KleisliCategory B 
K_T = record {
          FObj = FObj F_K
        ; FMap = kfmap
        ; isFunctor = record
        {      ≈-cong   = ≈-cong
             ; identity = identity
             ; distr    = distr1
        }
     }  where
         identity : {a : Obj A} →  B [ kfmap (K-id {a}) ≈ id1 B (FObj F_K a) ]
         identity {a} = let open ≈-Reasoning (B) in
           begin
               kfmap (K-id {a})
           ≈⟨⟩
               TMap ε_K (FObj F_K a) o FMap F_K (KMap (K-id {a}))
           ≈⟨⟩
              TMap ε_K (FObj F_K a) o FMap F_K (TMap η_K a)
           ≈⟨ IsAdjunction.adjoint2 (isAdjunction AdjK) ⟩
              id1 B (FObj F_K a)
           ∎
         ≈-cong : {a b : Obj A} -> {f g : KHom a b} → A [ KMap f ≈ KMap g ] → B [ kfmap f ≈ kfmap g ]
         ≈-cong {a} {b} {f} {g} f≈g = let open ≈-Reasoning (B) in
           begin
               kfmap f
           ≈⟨⟩
               TMap ε_K (FObj F_K b) o FMap F_K (KMap f)
           ≈⟨ cdr ( fcong F_K f≈g)  ⟩
               TMap ε_K (FObj F_K b) o FMap F_K (KMap g)
           ≈⟨⟩
               kfmap g
           ∎
         distr1 :  {a b c : Obj A} {f : KHom a b} {g : KHom b c} → B [ kfmap (g * f) ≈ (B [ kfmap g o kfmap f ] )]
         distr1 {a} {b} {c} {f} {g} = let open ≈-Reasoning (B) in
           begin
              kfmap (g * f)
           ≈⟨⟩
              TMap ε_K (FObj F_K c) o FMap F_K (KMap (g * f))
           ≈⟨⟩
              TMap ε_K (FObj F_K c) o FMap F_K (A [ TMap μ_K c o A [ FMap ( U_K ○ F_K ) (KMap g)  o KMap f ] ] )
           ≈⟨ cdr ( distr F_K ) ⟩
              TMap ε_K (FObj F_K c) o ( FMap F_K (TMap μ_K c) o ( FMap F_K (A  [ FMap ( U_K ○ F_K ) (KMap g)  o KMap f ])))
           ≈⟨ cdr (cdr ( distr F_K )) ⟩
              TMap ε_K (FObj F_K c) o ( FMap F_K (TMap μ_K c) o (( FMap F_K (FMap ( U_K ○ F_K ) (KMap g))) o (FMap F_K (KMap f))))
           ≈⟨ cdr assoc ⟩
              TMap ε_K (FObj F_K c) o ((( FMap F_K (TMap μ_K c) o ( FMap F_K (FMap (U_K ○ F_K) (KMap g))))) o (FMap F_K (KMap f)))
           ≈⟨⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) )) o 
                                  ( FMap F_K (FMap (U_K ○ F_K) (KMap g)))) o (FMap F_K (KMap f)))
           ≈⟨ sym (cdr assoc)  ⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) ))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (KMap g))) o (FMap F_K (KMap f))))
           ≈⟨ assoc ⟩
              (TMap ε_K (FObj F_K c) o ( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) )))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (KMap g))) o (FMap F_K (KMap f)))
           ≈⟨ car (sym (nat ε_K)) ⟩
              (TMap ε_K (FObj F_K c) o ( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (KMap g))) o (FMap F_K (KMap f)))
           ≈⟨ sym assoc ⟩
              TMap ε_K (FObj F_K c) o (( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c))) o 
                                  ((( FMap F_K (FMap (U_K ○ F_K) (KMap g)))) o (FMap F_K (KMap f))))
           ≈⟨ cdr assoc ⟩
              TMap ε_K (FObj F_K c) o ((( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (KMap g))))) o (FMap F_K (KMap f)))
           ≈⟨ cdr ( car (
               begin
                    TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)) o ((FMap F_K (FMap (U_K ○ F_K) (KMap g))))
                 ≈⟨⟩
                    TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)) o  (FMap (F_K ○ U_K) (FMap F_K (KMap g))) 
                 ≈⟨ sym (nat ε_K)  ⟩
                    ( FMap F_K (KMap g)) o (TMap ε_K (FObj F_K b))
               ∎
           ))  ⟩
              TMap ε_K (FObj F_K c) o ((( FMap F_K (KMap g)) o (TMap ε_K (FObj F_K b))) o FMap F_K (KMap f))
           ≈⟨ cdr (sym assoc) ⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K (KMap g)) o (TMap ε_K (FObj F_K b) o FMap F_K (KMap f)))
           ≈⟨ assoc ⟩
              (TMap ε_K (FObj F_K c) o FMap F_K (KMap g)) o (TMap ε_K (FObj F_K b) o FMap F_K (KMap f))
           ≈⟨⟩
              kfmap g o kfmap f
           ∎

Lemma-K1 : {a b : Obj A} ( f : Hom A a b ) -> B [ FMap K_T ( FMap F_T f)  ≈ FMap F_K f ]
Lemma-K1 {a} {b} f = let open ≈-Reasoning (B) in
           begin
             FMap K_T ( FMap F_T f)  
           ≈⟨⟩
             TMap ε_K (FObj F_K b) o FMap F_K (KMap( FMap F_T f))
           ≈⟨⟩
             TMap ε_K (FObj F_K b) o FMap F_K (A [ TMap η_K b o f ])
           ≈⟨ cdr ( distr F_K) ⟩
             TMap ε_K (FObj F_K b) o (FMap F_K (TMap η_K b)  o FMap F_K f )
           ≈⟨ assoc  ⟩
             (TMap ε_K (FObj F_K b) o FMap F_K (TMap η_K b))  o FMap F_K f 
           ≈⟨ car ( IsAdjunction.adjoint2 (isAdjunction AdjK)) ⟩
             id1 B (FObj F_K b)  o FMap F_K f 
           ≈⟨ idL  ⟩
             FMap F_K f 
           ∎

Lemma-K2 : {a b : Obj A} ( f : KHom a b ) -> A [ FMap U_K ( FMap K_T f)  ≈ FMap U_T f ]
Lemma-K2 {a} {b} f = let open ≈-Reasoning (A) in
           begin
              FMap U_K ( FMap K_T f)
           ≈⟨⟩
              FMap U_K ( B [  TMap ε_K (FObj F_K b) o FMap F_K (KMap f) ] )
           ≈⟨ distr U_K ⟩
              FMap U_K ( TMap ε_K (FObj F_K b)) o FMap U_K (FMap F_K (KMap f) )
           ≈⟨⟩  
              TMap μ_K b o FMap T_K (KMap f) 
           ≈⟨⟩  -- the definition
              FMap U_T f
           ∎

Lemma-K3 : (b : Obj A)  -> B [ FMap K_T (record { KMap = (TMap η_K b) }) ≈ id1 B (FObj F_K b) ]
Lemma-K3 b = let open ≈-Reasoning (B) in
           begin
                 FMap K_T  (record { KMap = (TMap η_K b) })
           ≈⟨⟩  
                 TMap ε_K (FObj F_K b) o FMap F_K (TMap η_K b)
           ≈⟨  IsAdjunction.adjoint2 (isAdjunction AdjK) ⟩  
                 id1 B (FObj F_K b)
           ∎

Lemma-K4 : (b c : Obj A) (g : Hom A b (FObj T_K c)) -> 
     B [ FMap K_T ( record { KMap = A [ (TMap η_K (FObj T_K c)) o g ] })  ≈ FMap F_K g ]
Lemma-K4 b c g = let open ≈-Reasoning (B) in
           begin
                FMap K_T ( record { KMap = A [ (TMap η_K (FObj T_K c)) o g ] }) 
           ≈⟨⟩
                TMap ε_K (FObj F_K (FObj T_K c)) o FMap F_K (A [ (TMap η_K (FObj T_K c)) o g ])
           ≈⟨ cdr (distr F_K) ⟩
                TMap ε_K (FObj F_K (FObj T_K c)) o ( FMap F_K (TMap η_K (FObj T_K c)) o FMap F_K g )
           ≈⟨ assoc ⟩
                (TMap ε_K (FObj F_K (FObj T_K c)) o ( FMap F_K (TMap η_K (FObj T_K c)))) o FMap F_K g 
           ≈⟨ car ( IsAdjunction.adjoint2 (isAdjunction AdjK)) ⟩  
                 id1 B (FObj F_K (FObj T_K c)) o FMap F_K g 
           ≈⟨ idL ⟩
                FMap F_K g 
           ∎

-- Lemma-K5 : (a : Obj A) -> FObj U_K ( FObj K_T a ) = U_T a

Lemma-K6 : (b c : Obj A) (g : KHom b c) -> A [ FMap U_K ( FMap K_T g )  ≈ FMap U_T g ]
Lemma-K6 b c g =  let open ≈-Reasoning (A) in
           begin
                 FMap U_K ( FMap K_T g )
           ≈⟨⟩
                 FMap U_K ( B [ TMap ε_K ( FObj F_K c )  o FMap F_K (KMap g) ] )
           ≈⟨ distr U_K ⟩
                 FMap U_K ( TMap ε_K ( FObj F_K c ))  o FMap U_K ( FMap F_K (KMap g) )
           ≈⟨⟩
                 TMap μ_K c o FMap U_K ( FMap F_K (KMap g) )
           ≈⟨⟩
                 FMap U_T g
           ∎


