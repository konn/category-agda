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

module adj-monad where

----
--
-- Adjunction to Monad
--
----

open Adjunction
open NTrans
open Functor

UεF :  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                 ( U : Functor B A )
                 ( F : Functor A B )
                 ( ε : NTrans B B  ( F ○  U ) identityFunctor ) → NTrans A A  (( U ○  F ) ○ ( U ○  F )) ( U ○  F )
UεF A B U F ε =  lemma11  (
     Functor*Nat A {B} A U {( F ○ U) ○ F} {identityFunctor ○ F} ( Nat*Functor A {B} B { F ○  U} {identityFunctor} ε F)  ) where
         lemma11 :   NTrans A A   ( U ○ ((F  ○  U) ○  F )) ( U ○  (identityFunctor ○ F) ) 
                  →  NTrans A A  (( U ○  F ) ○ ( U ○  F )) ( U ○  F )
         lemma11  n = record { TMap = \a → TMap n a; isNTrans = record { commute = IsNTrans.commute ( isNTrans n ) }}

Adj2Monad : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')
                 { U : Functor B A }
                 { F : Functor A B }
                 { η : NTrans A A identityFunctor ( U ○  F ) }
                 { ε : NTrans B B  ( F ○  U ) identityFunctor } →
      Adjunction A B U F η ε  → Monad A (U ○  F) η (UεF A B U F ε)
Adj2Monad A B {U} {F} {η} {ε} adj = record {
         isMonad = record {
                    assoc = assoc1;
                    unity1 = unity1;
                    unity2 = unity2
              }
      }  where
           T : Functor A A
           T = U  ○ F
           μ : NTrans A A ( T ○ T ) T
           μ = UεF A B U F ε
           lemma-assoc1 : {a b : Obj B} → ( f : Hom B a b) → 
                 B [ B [ f o TMap ε a ] ≈ B [ TMap ε b o FMap F (FMap U f ) ] ] 
           lemma-assoc1 f =  IsNTrans.commute ( isNTrans ε )
           assoc1 : {a : Obj A} → A [ A [ TMap μ a o TMap μ ( FObj T a ) ] ≈  A [  TMap μ a o FMap T (TMap μ a) ] ]
           assoc1 {a} = let open ≈-Reasoning (A) in
             begin
                TMap μ a o TMap μ ( FObj T a )
             ≈⟨⟩
                (FMap U (TMap ε ( FObj F a ))) o (FMap U (TMap ε ( FObj F ( FObj U (FObj F  a )))))
             ≈⟨ sym (distr U) ⟩
                FMap U (B [ TMap ε ( FObj F a )  o TMap ε ( FObj F ( FObj U (FObj F a ))) ] )
             ≈⟨  (IsFunctor.≈-cong (isFunctor U)) (lemma-assoc1 ( TMap ε (FObj F a ))) ⟩
                FMap U (B [ (TMap ε ( FObj F a )) o FMap F (FMap U (TMap ε ( FObj F a ))) ] )
             ≈⟨ distr U ⟩
                (FMap U (TMap ε ( FObj F a ))) o FMap U (FMap F (FMap U (TMap ε ( FObj F a ))))
             ≈⟨⟩
                TMap μ a o FMap T (TMap μ a) 
             ∎
           unity1 : {a : Obj A} → A [ A [ TMap μ a o TMap η ( FObj T a ) ] ≈ Id {_} {_} {_} {A} (FObj T a) ]
           unity1 {a} = let open ≈-Reasoning (A) in
             begin
               TMap μ a o TMap η ( FObj T a )
             ≈⟨⟩
               (FMap U (TMap ε ( FObj F a ))) o TMap η ( FObj U ( FObj F  a ))
             ≈⟨ IsAdjunction.adjoint1 ( isAdjunction adj ) ⟩
               id (FObj U ( FObj F a ))
             ≈⟨⟩
               id (FObj T a)
             ∎
           unity2 : {a : Obj A} → A [ A [ TMap μ a o (FMap T (TMap η a ))] ≈ Id {_} {_} {_} {A} (FObj T a) ]
           unity2 {a} = let open ≈-Reasoning (A) in
             begin
                TMap μ a o (FMap T (TMap η a ))
             ≈⟨⟩
                (FMap U (TMap ε ( FObj F a ))) o (FMap U ( FMap F (TMap η a )))
             ≈⟨ sym (distr U ) ⟩
                FMap U ( B [  (TMap ε ( FObj F a )) o ( FMap F (TMap η a )) ])
             ≈⟨ (IsFunctor.≈-cong (isFunctor U)) (IsAdjunction.adjoint2 ( isAdjunction adj )) ⟩
                FMap U ( id1 B (FObj F a) )
             ≈⟨ IsFunctor.identity ( isFunctor U ) ⟩
                id (FObj T a)
             ∎
