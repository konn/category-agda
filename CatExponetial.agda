----
--
--  B^A
--                        Shinji KONO <kono@ie.u-ryukyu.ac.jp>
----

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
module CatExponetial where 

--  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} {A : Category c₁ c₂ ℓ} {B : Category c₁' c₂' ℓ' }

open import HomReasoning
open import cat-utility


-- Object is a Functor : A → B 
-- Hom is a natural transformation

open Functor

CObj = λ {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ')  → Functor A B
CHom = λ {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ') (f g : CObj A B )  → NTrans A B f g

open NTrans 
Cid : {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ' ) {a : CObj A B } → CHom A B a a
Cid {c₁} {c₂} {ℓ} {c₁'} {c₂'} {ℓ'} A B {a} = record { TMap = \x -> id1 B (FObj a x) ; isNTrans = isNTrans1 {a} } where
   commute : {a : CObj A B } {a₁ b : Obj A} {f : Hom A a₁ b} →
        B [ B [ FMap a f o id1 B (FObj a a₁) ] ≈
        B [ id1 B (FObj a b) o FMap a f ] ]
   commute {a} {a₁} {b} {f} = let open ≈-Reasoning B in begin
                 FMap a f o id1 B (FObj a a₁) 
             ≈⟨ idR ⟩
                 FMap a f 
             ≈↑⟨ idL ⟩
                 id1 B (FObj a b) o FMap a f
             ∎
   isNTrans1 : {a : CObj A B } → IsNTrans A B a a (\x -> id1 B (FObj a x))
   isNTrans1 {a} = record { commute = \{a₁ b f} -> commute {a} {a₁} {b} {f} }

_+_ :  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} {A : Category c₁ c₂ ℓ} {B : Category c₁' c₂' ℓ' }  {a b c : CObj A B } 
     → CHom A B b c → CHom A B a b → CHom A B a c
_+_  {c₁} {c₂} {ℓ} {c₁'} {c₂'} {ℓ'} {A} {B}  {a} {b} {c} f g  = record { TMap = λ x → B [ TMap f x o TMap g x ] ; isNTrans = isNTrans1  } where
   commute1 :  (a b c : CObj A B ) (f : CHom  A B b c)  (g : CHom A B a b ) 
            (a₁ b₁ : Obj A) (h : Hom A a₁ b₁) →
                        B [ B [ FMap c h o B [ TMap f a₁ o TMap g a₁ ] ] ≈
                        B [ B [ TMap f b₁ o TMap g b₁ ] o FMap a h ] ]
   commute1  a b c f g a₁ b₁ h =   let open ≈-Reasoning B in begin
                B [ FMap c h o B [ TMap f a₁ o TMap g a₁ ] ]
             ≈⟨ assoc  ⟩
                B [ B [ FMap c h o TMap f a₁ ] o TMap g a₁ ] 
             ≈⟨ car (nat f) ⟩
                B [ B [ TMap f b₁ o FMap b h ] o TMap g a₁ ] 
             ≈↑⟨ assoc ⟩
                B [ TMap f b₁ o B [ FMap b h  o TMap g a₁ ]  ]
             ≈⟨ cdr (nat g) ⟩
                B [ TMap f b₁ o B [ TMap g b₁  o FMap a h ]  ]
             ≈⟨ assoc ⟩
                B [ B [ TMap f b₁ o TMap g b₁ ] o FMap a h ] 
             ∎ 
   isNTrans1 : IsNTrans A B a c (λ x → B [ TMap f x o TMap g x ]) 
   isNTrans1 = record { commute = λ {a₁ b₁ h} → commute1 a b c f g a₁ b₁ h }

_==_  :  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} {A : Category c₁ c₂ ℓ} {B : Category c₁' c₂' ℓ' } {a b : CObj A B } → 
    CHom A B a b → CHom A B a b  → Set (ℓ' ⊔ c₁)
_==_  {c₁} {c₂} {ℓ} {c₁'} {c₂'} {ℓ'} {A} {B} {a} {b} f g =  ∀{x} → B [ TMap f x  ≈  TMap g x  ]

infix  4 _==_

open import Relation.Binary.Core  
isB^A :  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level} (A : Category c₁ c₂ ℓ) (B : Category c₁' c₂' ℓ' ) → IsCategory (CObj A B) (CHom A B) _==_ _+_ (Cid A B)
isB^A  {c₁} {c₂} {ℓ} {c₁'} {c₂'} {ℓ'} A B =
  record  { isEquivalence =  record {refl = IsEquivalence.refl (IsCategory.isEquivalence ( Category.isCategory B )); 
                  sym = \{i j} → sym1 {_} {_} {i} {j} ;
                  trans = \{i j k} → trans1 {_} {_} {i} {j} {k} }  
        ; identityL = IsCategory.identityL ( Category.isCategory B )
        ; identityR = IsCategory.identityR ( Category.isCategory B )
        ; o-resp-≈ =  λ{a b c f g h i } → o-resp-≈1      {a} {b} {c} {f} {g} {h} {i}
        ; associative = IsCategory.associative ( Category.isCategory B )
        } where
            sym1 : {a b : CObj A B } {i j : CHom A B a b } → i == j → j == i
            sym1 {a} {b} {i} {j} eq {x} = let open ≈-Reasoning B in begin
                 TMap j x
             ≈⟨ sym eq ⟩
                 TMap i x
             ∎ 
            trans1 : {a b : CObj A B } {i j k : CHom A B a b} → i == j → j == k → i == k
            trans1 {a} {b} {i} {j} {k} i=j j=k {x} =  let open ≈-Reasoning B in begin
                 TMap i x
             ≈⟨ i=j ⟩
                 TMap j x
             ≈⟨ j=k ⟩
                 TMap k x
             ∎
            o-resp-≈1 : {a b c : CObj A B } {f g : CHom A B a b} {h i : CHom A B b c } → 
                f == g → h == i → h + f == i + g
            o-resp-≈1 {a} {b} {c} {f} {g} {h} {i} f=g h=i {x} = let open ≈-Reasoning B in begin
                 TMap h x  o TMap f x
             ≈⟨ resp f=g h=i ⟩
                 TMap i x  o TMap g x
             ∎

_^_ :  {c₁ c₂ ℓ c₁' c₂' ℓ' : Level}  (A : Category c₁' c₂' ℓ' ) (B : Category c₁ c₂ ℓ) →  
     Category (suc ℓ' ⊔ (suc c₂' ⊔ (suc c₁' ⊔ (suc ℓ ⊔ (suc c₂ ⊔ suc c₁))))) 
              (suc ℓ' ⊔ (suc c₂' ⊔ (suc c₁' ⊔ (suc ℓ ⊔ (suc c₂ ⊔ suc c₁)))))   
              (ℓ' ⊔ c₁)
_^_ {c₁} {c₂} {ℓ} {c₁'} {c₂'} {ℓ'} B A =
  record { Obj = CObj A B
         ; Hom = CHom A B
         ; _o_ = _+_
         ; _≈_ = _==_
         ; Id  = Cid A B
         ; isCategory = isB^A A B
         }

