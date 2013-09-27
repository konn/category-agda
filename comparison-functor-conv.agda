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


module comparison-functor-conv
      { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ }
                 { T : Functor A A }
                 { η : NTrans A A identityFunctor T }
                 { μ : NTrans A A (T ○ T) T }
                 { M' : Monad A T η μ }
      {c₁' c₂' ℓ' : Level} ( B : Category c₁' c₂' ℓ' ) 
      { U_K : Functor B A } { F_K : Functor A B }
      { η_K : NTrans A A identityFunctor ( U_K ○ F_K ) }
      { ε_K : NTrans B B ( F_K ○ U_K ) identityFunctor } 
      { μ_K : NTrans A A (( U_K ○ F_K ) ○ ( U_K ○ F_K )) ( U_K ○ F_K ) } 
      ( M :  Monad A (U_K ○ F_K) η_K μ_K )
      ( AdjK : Adjunction A B U_K F_K η_K ε_K )
      ( RK : MResolution A B T U_K F_K {η_K} {ε_K} {μ_K} AdjK )
  where

open import kleisli {c₁} {c₂} {ℓ} {A} { T } { η } { μ } { M' } 
open Functor
open NTrans
open Category.Cat.[_]_~_
open MResolution

≃-sym : {c₁ c₂ ℓ : Level} { C : Category c₁ c₂ ℓ } {c₁' c₂' ℓ' : Level} { D : Category c₁' c₂' ℓ' } 
      {F G : Functor C D} → F ≃ G → G ≃ F
≃-sym {_} {_} {_} {C} {_} {_} {_} {D} {F} {G} F≃G f = helper (F≃G f)
  where
    helper : ∀{a b c d} {f : Hom D a b} {g : Hom D c d} → [ D ] f ~ g → [ D ] g ~ f
    helper (Category.Cat.refl Ff≈Gf) = 
                   Category.Cat.refl {C = D} (IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory D)) Ff≈Gf)

-- to T=UF constraints happy 
hoge : {c₁ c₂ ℓ : Level} { C : Category c₁ c₂ ℓ } {c₁' c₂' ℓ' : Level} { D : Category c₁' c₂' ℓ' } 
      {F G : Functor C D} → F ≃ G → F ≃ G
hoge {_} {_} {_} {C} {_} {_} {_} {D} {F} {G} F≃G f = helper (F≃G f)
  where
    helper : ∀{a b c d} {f : Hom D a b} {g : Hom D c d} → [ D ] f ~ g → [ D ] f ~ g
    helper (Category.Cat.refl Ff≈Gf) = Category.Cat.refl Ff≈Gf

open KleisliHom

RHom  = \(a b : Obj A) -> KleisliHom {c₁} {c₂} {ℓ} {A} { U_K ○ F_K } a b
TtoK : (a b : Obj A) -> (KHom a b) ->  {g h : Hom A  (FObj T b) (FObj ( U_K ○ F_K) b) } ->
      ([ A ] g ~ h) -> Hom A a (FObj ( U_K ○ F_K ) b)  
TtoK  _ _ f {g} (Category.Cat.refl _) = A [ g o (KMap f) ]
TKMap : {a b : Obj A} -> (f : KHom a b) -> Hom A a (FObj ( U_K ○ F_K ) b) 
TKMap  {a} {b} f = TtoK a b f {_} {_} ((hoge (T=UF RK)) (id1 A b)) 

KtoT : (a b : Obj A) -> (RHom a b) -> {g h : Hom A  (FObj ( U_K ○ F_K ) b) (FObj  T b) } ->
      ([ A ] g ~ h) -> Hom A a (FObj T b)  
KtoT  _ _ f {g} {h} (Category.Cat.refl eq) = A [ g o (KMap f) ]
KTMap : {a b : Obj A} -> (f : RHom a b) -> Hom A a (FObj T b) 
KTMap {a} {b} f = KtoT a b f {_} {_}  (( ≃-sym (T=UF RK)) (id1 A b))

TKMap-cong : {a b : Obj A} {f g : KHom a b} -> A [ KMap f ≈ KMap g ] -> A [ TKMap f ≈ TKMap g ]
TKMap-cong {a} {b} {f} {g} eq = helper a b f g eq ((hoge (T=UF RK))( id1 A b  )) 
  where 
        open ≈-Reasoning (A)
        helper : (a b : Obj A) (f g : KHom a b) -> A [ KMap f ≈ KMap g ] ->
                 {conv : Hom A  (FObj T b) (FObj ( U_K ○ F_K ) b) } -> ([ A ] conv ~ conv) -> A [ TKMap f ≈ TKMap g ]
        helper _ _ _ _ eq (Category.Cat.refl _) = 
            (Category.IsCategory.o-resp-≈ (Category.isCategory A)) eq refl-hom

kfmap : {a b : Obj A} (f : KHom a b) -> Hom B (FObj F_K a) (FObj F_K b)
kfmap {_} {b} f = B [ TMap ε_K (FObj F_K b) o FMap F_K (TKMap f) ]

open Adjunction
K_T : Functor KleisliCategory B 
K_T = record {
          FObj = FObj F_K
        ; FMap = kfmap
        ; isFunctor = record
        {      ≈-cong   = ≈-cong
             ; identity = identity
             ; distr    = distr1
        }
     } where
         identity : {a : Obj A} →  B [ kfmap (K-id {a}) ≈ id1 B (FObj F_K a) ]
         identity {a} = let open ≈-Reasoning (B) in
           begin
               kfmap (K-id {a})
           ≈⟨⟩
               TMap ε_K (FObj F_K a) o FMap F_K (TKMap (K-id {a}))
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
               TMap ε_K (FObj F_K b) o FMap F_K (TKMap f)
           ≈⟨ cdr ( fcong F_K (TKMap-cong f≈g))  ⟩
               TMap ε_K (FObj F_K b) o FMap F_K (TKMap g)
           ≈⟨⟩
               kfmap g
           ∎
         distr1 :  {a b c : Obj A} {f : KHom a b} {g : KHom b c} → B [ kfmap (g * f) ≈ (B [ kfmap g o kfmap f ] )]
         distr1 {a} {b} {c} {f} {g} = let open ≈-Reasoning (B) in
           begin
              kfmap (g * f)
           ≈⟨⟩
              TMap ε_K (FObj F_K c) o FMap F_K (TKMap (g * f))
           ≈⟨⟩
              TMap ε_K (FObj F_K c) o FMap F_K (A [ TMap μ_K c o A [ FMap ( U_K ○ F_K ) (TKMap g)  o TKMap f ] ] )
           ≈⟨ cdr ( distr F_K ) ⟩
              TMap ε_K (FObj F_K c) o ( FMap F_K (TMap μ_K c) o ( FMap F_K (A  [ FMap ( U_K ○ F_K ) (TKMap g)  o TKMap f ])))
           ≈⟨ cdr (cdr ( distr F_K )) ⟩
              TMap ε_K (FObj F_K c) o ( FMap F_K (TMap μ_K c) o (( FMap F_K (FMap ( U_K ○ F_K ) (TKMap g))) o (FMap F_K (TKMap f))))
           ≈⟨ cdr assoc ⟩
              TMap ε_K (FObj F_K c) o ((( FMap F_K (TMap μ_K c) o ( FMap F_K (FMap (U_K ○ F_K) (TKMap g))))) o (FMap F_K (TKMap f)))
           ≈⟨ cdr (car (car ( fcong F_K ( μ=UεF RK )))) ⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) )) o 
                                  ( FMap F_K (FMap (U_K ○ F_K) (TKMap g)))) o (FMap F_K (TKMap f)))
           ≈⟨ sym (cdr assoc)  ⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) ))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (TKMap g))) o (FMap F_K (TKMap f))))
           ≈⟨ assoc ⟩
              (TMap ε_K (FObj F_K c) o ( FMap F_K ( FMap U_K ( TMap ε_K ( FObj F_K c ) )))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (TKMap g))) o (FMap F_K (TKMap f)))
           ≈⟨ car (sym (nat ε_K)) ⟩
              (TMap ε_K (FObj F_K c) o ( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (TKMap g))) o (FMap F_K (TKMap f)))
           ≈⟨ sym assoc ⟩
              TMap ε_K (FObj F_K c) o (( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c))) o 
                                  ((( FMap F_K (FMap (U_K ○ F_K) (TKMap g)))) o (FMap F_K (TKMap f))))
           ≈⟨ cdr assoc ⟩
              TMap ε_K (FObj F_K c) o ((( TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c))) o 
                                  (( FMap F_K (FMap (U_K ○ F_K) (TKMap g))))) o (FMap F_K (TKMap f)))
           ≈⟨ cdr ( car (
               begin
                    TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)) o ((FMap F_K (FMap (U_K ○ F_K) (TKMap g))))
                 ≈⟨⟩
                    TMap ε_K (FObj (F_K ○ U_K) (FObj F_K c)) o  (FMap (F_K ○ U_K) (FMap F_K (TKMap g))) 
                 ≈⟨ sym (nat ε_K)  ⟩
                    ( FMap F_K (TKMap g)) o (TMap ε_K (FObj F_K b))
               ∎
           ))  ⟩
              TMap ε_K (FObj F_K c) o ((( FMap F_K (TKMap g)) o (TMap ε_K (FObj F_K b))) o FMap F_K (TKMap f))
           ≈⟨ cdr (sym assoc) ⟩
              TMap ε_K (FObj F_K c) o (( FMap F_K (TKMap g)) o (TMap ε_K (FObj F_K b) o FMap F_K (TKMap f)))
           ≈⟨ assoc ⟩
              (TMap ε_K (FObj F_K c) o FMap F_K (TKMap g)) o (TMap ε_K (FObj F_K b) o FMap F_K (TKMap f))
           ≈⟨⟩
              kfmap g o kfmap f
           ∎

