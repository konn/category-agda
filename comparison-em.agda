-- -- -- -- -- -- -- -- 
--  Comparison Functor of  Eilenberg-Moore  Category
--  defines U^K and F^K as a resolution of Monad
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

module comparison-em 
      { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ }
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { M' : Monad A T η μ }
      {c₁' c₂' ℓ' : Level} ( B : Category c₁' c₂' ℓ' ) 
      { U^K : Functor B A } { F^K : Functor A B }
      { η^K : NTrans A A identityFunctor ( U^K ○ F^K ) }
      { ε^K : NTrans B B ( F^K ○ U^K ) identityFunctor } 
      { μ^K : NTrans A A (( U^K ○ F^K ) ○ ( U^K ○ F^K )) ( U^K ○ F^K ) }
      ( Adj^K : Adjunction A B U^K F^K η^K ε^K )
      ( RK : MResolution A B T U^K F^K {η^K} {ε^K} {μ^K} Adj^K )
where

open import adj-monad

T^K = U^K ○ F^K

μ^K' : NTrans A A (( U^K ○ F^K ) ○ ( U^K ○ F^K )) ( U^K ○ F^K ) 
μ^K'  = UεF A B U^K F^K ε^K 

M : Monad A (U^K ○ F^K ) η^K μ^K' 
M =  Adj2Monad A B {U^K} {F^K} {η^K} {ε^K} Adj^K

open import em-category {c₁} {c₂} {ℓ} {A} { U^K ○ F^K } { η^K } { μ^K' } { M } 

open Functor
open NTrans
open Adjunction
open MResolution
open Eilenberg-Moore-Hom

emkobj : Obj B -> EMObj
emkobj b = record { 
     a = FObj U^K b ; phi = FMap U^K (TMap ε^K b) ; isAlgebra = record { identity = identity1 b; eval = eval1 b }
  } where
      identity1 :  (b : Obj B) -> A [ A [ (FMap U^K (TMap ε^K b))  o TMap η^K (FObj U^K b) ] ≈ id1 A (FObj U^K b) ]
      identity1 b =  let open ≈-Reasoning (A) in
           begin
                (FMap U^K (TMap ε^K b))  o TMap η^K (FObj U^K b)
           ≈⟨ IsAdjunction.adjoint1 (isAdjunction Adj^K) ⟩
                id1 A (FObj U^K b)
           ∎

      eval1 :  (b : Obj B) -> A [ A [ (FMap U^K (TMap ε^K b))  o TMap μ^K' (FObj U^K b) ] ≈ A [ (FMap U^K (TMap ε^K b)) o FMap T^K (FMap U^K (TMap ε^K b)) ] ]
      eval1 b = let open ≈-Reasoning (A) in
           begin
                (FMap U^K (TMap ε^K b)) o TMap μ^K' (FObj U^K b) 
           ≈⟨⟩
                (FMap U^K (TMap ε^K b)) o FMap U^K (TMap ε^K ( FObj F^K (FObj U^K b)))
           ≈⟨ sym (distr U^K) ⟩
                FMap U^K (B [ TMap ε^K b o (TMap ε^K ( FObj F^K (FObj U^K b))) ] )
           ≈⟨ fcong U^K (nat ε^K) ⟩   -- Horizontal composition
                FMap U^K (B [ TMap ε^K b o FMap F^K (FMap U^K (TMap ε^K b)) ] )
           ≈⟨ distr U^K ⟩
                (FMap U^K (TMap ε^K b)) o FMap U^K (FMap F^K (FMap U^K (TMap ε^K b)))
           ≈⟨⟩
                (FMap U^K (TMap ε^K b)) o FMap T^K (FMap U^K (TMap ε^K b))
           ∎


open EMObj
emkmap : {a b : Obj B} (f : Hom B a b) -> EMHom (emkobj a) (emkobj b)
emkmap {a} {b} f = record { EMap = FMap U^K f ; homomorphism = homomorphism1 a b f
  } where
      homomorphism1 : (a b : Obj B) (f : Hom B a b) -> A [ A [ (φ (emkobj b))  o FMap T^K (FMap U^K f) ]  ≈ A [ (FMap U^K f) o (φ (emkobj a)) ] ]
      homomorphism1 a b f = let open ≈-Reasoning (A) in
           begin
                (φ (emkobj b))  o FMap T^K (FMap U^K f)
           ≈⟨⟩
                FMap U^K (TMap ε^K b)  o FMap U^K (FMap F^K (FMap U^K f))
           ≈⟨ sym (distr U^K) ⟩
                FMap U^K ( B [ TMap ε^K b  o FMap F^K (FMap U^K f) ] )
           ≈⟨ sym (fcong U^K (nat ε^K)) ⟩
                FMap U^K ( B [ f o TMap ε^K a ] )
           ≈⟨ distr U^K ⟩
                (FMap U^K f) o FMap U^K (TMap ε^K a)
           ≈⟨⟩
                (FMap U^K f) o ( φ (emkobj a))
           ∎


K^T : Functor B Eilenberg-MooreCategory 
K^T = record {
          FObj = emkobj
        ; FMap = emkmap
        ; isFunctor = record
        {      ≈-cong   = ≈-cong
             ; identity = identity
             ; distr    = distr1
        }
     }  where
         identity : {a : Obj B} →   emkmap (id1 B a) ≗ EM-id {emkobj a}
         identity {a} = let open ≈-Reasoning (A) in
           begin
              EMap (emkmap (id1 B a))
           ≈⟨⟩
              FMap U^K (id1 B a) 
           ≈⟨ IsFunctor.identity (isFunctor U^K) ⟩
              id1 A ( FObj U^K a )
           ≈⟨⟩
              EMap (EM-id {emkobj a})
           ∎
         ≈-cong : {a b : Obj B} -> {f g : Hom B a b} → B [ f ≈ g ] →  emkmap f ≗ emkmap g 
         ≈-cong {a} {b} {f} {g} f≈g = let open ≈-Reasoning (A) in
           begin
               EMap (emkmap f)
           ≈⟨ IsFunctor.≈-cong (isFunctor U^K) f≈g ⟩
               EMap (emkmap g)
           ∎
         distr1 :  {a b c : Obj B} {f : Hom B a b} {g : Hom B b c} → ( (emkmap (B [ g o f ])) ≗  (emkmap g ∙ emkmap f)  )
         distr1 {a} {b} {c} {f} {g} = let open ≈-Reasoning (A) in
           begin
              EMap (emkmap (B [ g o f ] ))
           ≈⟨ distr U^K ⟩
              EMap (emkmap g ∙ emkmap f)
           ∎

Lemma-EM20 : { a b : Obj B} { f : Hom B a b } -> A [ FMap U^T ( FMap K^T f)  ≈ FMap U^K f ]
Lemma-EM20 {a} {b} {f}  =  let open ≈-Reasoning (A) in 
           begin
               FMap U^T ( FMap K^T f) 
           ≈⟨⟩
               FMap U^K f 
           ∎

-- Lemma-EM21 : { a : Obj B}  -> FObj U^T ( FObj K^T a)  = FObj U^K a 

Lemma-EM22 : { a b : Obj A} { f : Hom A a b } ->  A [ EMap ( FMap K^T ( FMap F^K f) ) ≈ EMap ( FMap F^T f  ) ]
Lemma-EM22  {a} {b} {f} =  let open ≈-Reasoning (A) in 
           begin
                EMap ( FMap K^T ( FMap F^K f) )
           ≈⟨⟩
                FMap U^K ( FMap F^K f)
           ≈⟨⟩
                EMap ( FMap F^T f  )
           ∎
 

-- Lemma-EM23 : { a b : Obj A}  ->  ( FObj K^T ( FObj F^K f) ) = ( FObj F^T f  ) 

-- Lemma-EM24 :  {a : Obj A } {b : Obj B} -> A [ TMap η^K (FObj U^K b) ≈ TMap η^K a ]
-- Lemma-EM24 = ?

Lemma-EM26 : {b : Obj B} -> A [ EMap (TMap ε^T ( FObj K^T b)) ≈ FMap U^K ( TMap ε^K b) ]
Lemma-EM26  {b} =  let open ≈-Reasoning (A) in 
           begin
                 EMap (TMap ε^T ( FObj K^T b))
           ≈⟨⟩
                 FMap U^K ( TMap ε^K b)
           ∎



