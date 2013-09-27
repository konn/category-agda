---
--
--  A → Sets^A^op  : Yoneda Functor
--     Contravariant Functor h_a
--     Nat(h_a,F)
--                        Shinji KONO <kono@ie.u-ryukyu.ac.jp>
----

open import Category -- https://github.com/konn/category-agda                                                                                     
open import Level
open import Category.Sets
module yoneda { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } where

open import HomReasoning
open import cat-utility
open import Relation.Binary.Core
open import Relation.Binary


-- Contravariant Functor : op A → Sets  ( Obj of Sets^{A^op} )
--   Obj and Hom of Sets^A^op

open Functor

YObj = Functor (Category.op A) (Sets {c₂})
YHom = λ (f : YObj ) → λ (g : YObj ) → NTrans (Category.op A) (Sets {c₂}) f g

open NTrans 
Yid : {a : YObj} → YHom a a
Yid {a} = record { TMap = \a -> \x -> x ; isNTrans = isNTrans1 {a} } where
   isNTrans1 : {a : YObj } → IsNTrans (Category.op A) (Sets {c₂}) a a (\a -> \x -> x )
   isNTrans1 {a} = record { commute = refl  }

_+_ : {a b c : YObj} → YHom b c → YHom a b → YHom a c
_+_{a} {b} {c} f g  = record { TMap = λ x → Sets [ TMap f x o TMap g x ] ; isNTrans = isNTrans1  } where
   commute1 :  (a b c : YObj ) (f : YHom  b c)  (g : YHom a b ) 
            (a₁ b₁ : Obj (Category.op A)) (h : Hom (Category.op A) a₁ b₁) →
                        Sets [ Sets [ FMap c h o Sets [ TMap f a₁ o TMap g a₁ ] ] ≈
                        Sets [ Sets [ TMap f b₁ o TMap g b₁ ] o FMap a h ] ]
   commute1  a b c f g a₁ b₁ h =   let open ≈-Reasoning (Sets {c₂})in begin
                Sets [ FMap c h o Sets [ TMap f a₁ o TMap g a₁ ] ]
             ≈⟨ assoc {_} {_} {_} {_} {FMap c h } {TMap f a₁} {TMap g a₁} ⟩
                Sets [ Sets [ FMap c h o TMap f a₁ ] o TMap g a₁ ] 
             ≈⟨ car (nat f) ⟩
                Sets [ Sets [ TMap f b₁ o FMap b h ] o TMap g a₁ ] 
             ≈↑⟨ assoc {_} {_} {_} {_} { TMap f b₁} {FMap b h } {TMap g a₁}⟩
                Sets [ TMap f b₁ o Sets [ FMap b h  o TMap g a₁ ]  ]
             ≈⟨ cdr {_} {_} {_} {_} {_} { TMap f b₁} (nat g) ⟩
                Sets [ TMap f b₁ o Sets [ TMap g b₁  o FMap a h ]  ]
             ≈↑⟨ assoc  {_} {_} {_} {_} {TMap f b₁} {TMap g b₁} { FMap a h}  ⟩
                Sets [ Sets [ TMap f b₁ o TMap g b₁ ] o FMap a h ] 
             ∎ 
   isNTrans1 : IsNTrans (Category.op A) (Sets {c₂}) a c (λ x → Sets [ TMap f x o TMap g x ]) 
   isNTrans1 = record { commute = λ {a₁ b₁ h} → commute1 a b c f g a₁ b₁ h }

_==_  :  {a b : YObj} → YHom a b → YHom a b → Set (c₂ ⊔ c₁)
_==_  f g = ∀{x : Obj (Category.op A)} → (Sets {c₂}) [ TMap f x ≈ TMap g x ]

infix  4 _==_

isSetsAop :  IsCategory YObj YHom _==_ _+_ Yid
isSetsAop  =  
  record  { isEquivalence =  record {refl = refl ; trans = \{i j k} → trans1 {_} {_} {i} {j} {k} ; sym = \{i j} → sym1  {_} {_} {i} {j}}
        ; identityL = refl
        ; identityR = refl
        ; o-resp-≈ =  λ{a b c f g h i } → o-resp-≈      {a} {b} {c} {f} {g} {h} {i}
        ; associative = refl
        } where
            sym1 : {a b : YObj } {i j : YHom a b } → i == j → j == i
            sym1 {a} {b} {i} {j} eq {x} = let open ≈-Reasoning (Sets {c₂}) in begin
                 TMap j x
             ≈⟨ sym eq ⟩
                 TMap i x
             ∎ 
            trans1 : {a b : YObj } {i j k : YHom a b} → i == j → j == k → i == k
            trans1 {a} {b} {i} {j} {k} i=j j=k {x} =  let open ≈-Reasoning (Sets {c₂}) in begin
                 TMap i x
             ≈⟨ i=j ⟩
                 TMap j x
             ≈⟨ j=k ⟩
                 TMap k x
             ∎
            o-resp-≈ : {A₁ B C : YObj} {f g : YHom A₁ B} {h i : YHom B C} → 
                f == g → h == i → h + f == i + g
            o-resp-≈ {a} {b} {c} {f} {g} {h} {i} f=g h=i {x} = let open ≈-Reasoning (Sets {c₂}) in begin
                 (Sets {c₂}) [ TMap h x  o TMap f x ]
             ≈⟨ resp f=g h=i ⟩
                 (Sets {c₂}) [ TMap i x  o TMap g x ]
             ∎

SetsAop : Category (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁))  (suc ℓ ⊔ (suc (suc c₂) ⊔ suc c₁)) (c₂ ⊔ c₁)
SetsAop =
  record { Obj = YObj
         ; Hom = YHom
         ; _o_ = _+_
         ; _≈_ = _==_
         ; Id  = Yid
         ; isCategory = isSetsAop
         }

-- A is Locally small
postulate ≈-≡ : {a b : Obj A } { x y : Hom A a b } →  (x≈y : A [ x ≈ y  ]) → x ≡ y

import Relation.Binary.PropositionalEquality
-- Extensionality a b = {A : Set a} {B : A → Set b} {f g : (x : A) → B x} → (∀ x → f x ≡ g x) → f ≡ g → ( λ x → f x ≡ λ x → g x )
postulate extensionality : Relation.Binary.PropositionalEquality.Extensionality c₂ c₂


----
--
--  Object mapping in Yoneda Functor
--
----

open import Function

y-obj : (a : Obj A) → Functor (Category.op A) (Sets {c₂})
y-obj a = record {
        FObj = λ b → Hom (Category.op A) a b  ;
        FMap =   λ {b c : Obj A } → λ ( f : Hom  A c b ) → λ (g : Hom  A b a ) →  (Category.op A) [ f o g ] ;
        isFunctor = record {
             identity =  \{b} → extensionality ( λ x → lemma-y-obj1 {b} x ) ;
             distr = λ {a} {b} {c} {f} {g} → extensionality ( λ x → lemma-y-obj2 a b c f g x ) ;
             ≈-cong = λ eq → extensionality ( λ x →  lemma-y-obj3 x eq ) 
        } 
    }  where
        lemma-y-obj1 : {b : Obj A } → (x : Hom A b a) →  (Category.op A) [ id1 A b o x ] ≡ x
        lemma-y-obj1 {b} x = let open ≈-Reasoning (Category.op A) in ≈-≡ idL
        lemma-y-obj2 :  (a₁ b c : Obj A) (f : Hom A b a₁) (g : Hom A c b ) → (x : Hom A a₁ a )→ 
               Category.op A [ Category.op A [ g o f ] o x ] ≡ (Sets [ _[_o_] (Category.op A) g o _[_o_] (Category.op A) f ]) x
        lemma-y-obj2 a₁ b c f g x = let open ≈-Reasoning (Category.op A) in ≈-≡ ( begin
               Category.op A [ Category.op A [ g o f ] o x ]
             ≈↑⟨ assoc ⟩
               Category.op A [ g o Category.op A [ f o x ] ]
             ≈⟨⟩
               ( λ x →  Category.op A [ g o x  ]  ) ( ( λ x → Category.op A [ f o x ] ) x )
             ∎ )
        lemma-y-obj3 :  {b c : Obj A} {f g : Hom A c b } → (x : Hom A b a ) → A [ f ≈ g ] →  Category.op A [ f o x ] ≡ Category.op A [ g o x ]
        lemma-y-obj3 {_} {_} {f} {g} x eq =  let open ≈-Reasoning (Category.op A) in ≈-≡   ( begin
                Category.op A [ f o x ]
             ≈⟨ resp refl-hom eq ⟩
                Category.op A [ g o x ]
             ∎ )


----
--
--  Hom mapping in Yoneda Functor
--
----

y-tmap :  ( a b : Obj A ) → (f : Hom A a b ) → (x : Obj (Category.op A)) → FObj (y-obj a) x → FObj (y-obj b ) x 
y-tmap  a b f x = λ ( g : Hom A x a ) → A [ f o g ]  --  ( h : Hom A x b ) 

y-map : {a b : Obj A } → (f : Hom A a b ) → YHom (y-obj a) (y-obj b) 
y-map {a} {b} f = record { TMap =  y-tmap  a b f ; isNTrans = isNTrans1 {a} {b} f } where
   lemma-y-obj4 : {a₁ b₁ : Obj (Category.op A)} {g : Hom (Category.op A) a₁ b₁} → {a b : Obj A } → (f : Hom A a b ) →
        Sets [ Sets [ FMap (y-obj b) g o y-tmap a b f a₁ ] ≈
        Sets [ y-tmap a b f b₁ o FMap (y-obj a) g ] ]
   lemma-y-obj4 {a₁} {b₁} {g} {a} {b} f = let open ≈-Reasoning A in extensionality ( λ x →  ≈-≡ ( begin
                A [ A [ f o x ] o g ]
             ≈↑⟨ assoc ⟩
                A [ f o A [ x  o g ] ]
             ∎ ) )
   isNTrans1 : {a b : Obj A } →  (f : Hom A a b ) → IsNTrans (Category.op A) (Sets {c₂}) (y-obj a) (y-obj b) (y-tmap a b f )
   isNTrans1 {a} {b} f = record { commute = λ{a₁ b₁ g } → lemma-y-obj4 {a₁} {b₁} {g} {a} {b} f } 

-----
--
-- Yoneda Functor itself
--
-----

YonedaFunctor : Functor A SetsAop
YonedaFunctor = record {
         FObj = λ a → y-obj a
       ; FMap = λ f → y-map f
       ; isFunctor = record {
             identity =  identity
             ; distr = distr1
             ; ≈-cong = ≈-cong

        } 
  } where
        ≈-cong : {a b : Obj A} {f g : Hom A a b} → A [ f ≈ g ] → SetsAop [ y-map f ≈ y-map g ]
        ≈-cong {a} {b} {f} {g} eq  =  let open ≈-Reasoning (A) in  -- (λ x g₁ → A [ f o g₁ ] ) ≡ (λ x g₁ → A [  g o  g₁ ] )
             extensionality ( λ h → ≈-≡  ( begin
                A [ f o h ]
             ≈⟨ resp refl-hom eq ⟩
                A [ g o h ]
             ∎
          ) ) 
        identity : {a : Obj A} → SetsAop [ y-map (id1 A a) ≈ id1 SetsAop (y-obj a )  ]
        identity  {a} =  let open ≈-Reasoning (A) in -- (λ x g → A [ id1 A a o g ] ) ≡ (λ a₁ x → x)
             extensionality ( λ g →  ≈-≡  ( begin
                A [ id1 A a o g ] 
             ≈⟨ idL ⟩
                g
             ∎
          ) )  
        distr1 : {a b c : Obj A} {f : Hom A a b} {g : Hom A b c} → SetsAop [ y-map (A [ g o f ]) ≈ SetsAop [ y-map g o y-map f ] ]
        distr1 {a} {b} {c} {f} {g} = let open ≈-Reasoning (A) in -- (λ x g₁ → (A [  (A [ g o f]  o g₁ ]))) ≡ (λ x x₁ → A [  g o A [ f o x₁ ] ] )
           extensionality ( λ h →  ≈-≡  ( begin
                A [ A [ g o f ]  o h ]
             ≈↑⟨ assoc  ⟩
                A [  g o A [ f o h ] ]
             ∎
          ) )  


------
--
--  F : A → Sets  ∈ Obj SetsAop
--
--  F(a) -> Nat(h_a,F)
--      x ∈ F(a) , (g : Hom A b a)  → ( FMap F g ) x
------

F2Natmap :  {a : Obj A} → {F : Obj SetsAop} → {x : FObj F a} → (b : Obj (Category.op A)) → Hom Sets (FObj (y-obj a) b) (FObj F b)
F2Natmap {a} {F} {x} b = λ ( g : Hom A b a ) → ( FMap F g ) x

F2Nat : {a : Obj A} → {F : Obj SetsAop} →  FObj F a  → Hom SetsAop (y-obj a) F
F2Nat {a} {F} x = record { TMap = F2Natmap {a} {F} {x} ; isNTrans = isNTrans1 } where
   commute1 : {a₁ b : Obj (Category.op A)} {f : Hom (Category.op A) a₁ b} (g : Hom A  a₁ a) →
                (Sets [ FMap F f o  FMap F g ]) x ≡ FMap F (A [ g o  f ] ) x
   commute1 g =  let open ≈-Reasoning (Sets) in
            cong ( λ f → f x ) ( sym ( distr F )  )
   commute : {a₁ b : Obj (Category.op A)} {f : Hom (Category.op A) a₁ b} → 
        Sets [ Sets [ FMap F f o F2Natmap {a} {F} {x} a₁ ] ≈ Sets [ F2Natmap {a} {F} {x} b o FMap (y-obj a) f ] ]
   commute {a₁} {b} {f} =  let open ≈-Reasoning (Sets) in
             begin
                Sets [ FMap F f o F2Natmap {a} {F} {x} a₁ ]
             ≈⟨⟩
                Sets [ FMap F f o (λ ( g : Hom A a₁ a ) → ( FMap F g ) x) ]
             ≈⟨ extensionality ( λ (g : Hom A  a₁ a) → commute1 {a₁} {b} {f} g ) ⟩
                Sets [  (λ ( g : Hom A b a ) → ( FMap F g ) x) o FMap (y-obj a) f ] 
             ≈⟨⟩
                Sets [ F2Natmap {a} {F} {x} b o FMap (y-obj a) f ] 
             ∎
   isNTrans1 : IsNTrans (Category.op A) (Sets {c₂}) (y-obj a) F (F2Natmap {a} {F})
   isNTrans1 = record { commute = λ {a₁ b f}  →  commute {a₁} {b} {f} } 


--  F(a) <- Nat(h_a,F)
Nat2F : {a : Obj A} → {F : Obj SetsAop} →  Hom SetsAop (y-obj a) F  → FObj F a 
Nat2F {a} {F} ha =  ( TMap ha a ) (id1 A a)

----
--
-- Prove  Bijection (as routine exercise ...)
--
----

F2Nat→Nat2F : {a : Obj A } → {F : Obj SetsAop} → (fa : FObj F a) →  Nat2F {a} {F} (F2Nat {a} {F} fa) ≡ fa 
F2Nat→Nat2F {a} {F} fa = let open ≈-Reasoning (Sets) in cong ( λ f → f fa ) (
             -- FMap F (Category.Category.Id A) fa ≡ fa
             begin
               ( FMap F (id1 A _ )) 
             ≈⟨ IsFunctor.identity (isFunctor F)    ⟩
                id1 Sets (FObj F a)
             ∎ )

open  import  Relation.Binary.PropositionalEquality

≡-cong = Relation.Binary.PropositionalEquality.cong 

--     F :  op A → Sets
--     ha : NTrans (op A) Sets (y-obj {a}) F
--                FMap F  g  o TMap ha a ≈   TMap ha b  o FMap (y-obj {a}) g

Nat2F→F2Nat : {a : Obj A } → {F : Obj SetsAop} → (ha : Hom SetsAop (y-obj a) F) →  SetsAop [ F2Nat {a} {F} (Nat2F {a} {F} ha) ≈ ha ]
Nat2F→F2Nat {a} {F} ha {b} = let open ≡-Reasoning in
             begin
                TMap (F2Nat {a} {F} (Nat2F {a} {F} ha)) b
             ≡⟨⟩
                (λ g → FMap F g (TMap ha a (Category.Category.Id A)))
             ≡⟨  extensionality (λ g → (
                begin
                    FMap F g (TMap ha a (Category.Category.Id A)) 
                ≡⟨  ≡-cong (λ f → f (Category.Category.Id A)) (IsNTrans.commute (isNTrans ha)) ⟩
                    TMap ha b (FMap (y-obj a) g (Category.Category.Id A))
                ≡⟨⟩
                    TMap ha b ( (A Category.o Category.Category.Id A) g )
                ≡⟨  ≡-cong ( TMap ha b ) ( ≈-≡ (IsCategory.identityL  ( Category.isCategory A ))) ⟩
                    TMap ha b g
                ∎ 
             )) ⟩
                TMap ha b
             ∎ 

-- Yoneda's Lemma
--    Yoneda Functor is full and faithfull
--    that is FMapp Yoneda is injective and surjective

--  λ b g → (A Category.o f₁) g
YondaLemma1 : {a a' : Obj A } {f : FObj (FObj YonedaFunctor a) a' } → SetsAop [ F2Nat {a'} {FObj YonedaFunctor a} f ≈ FMap YonedaFunctor f ]
YondaLemma1 {a} {a'} {f} = refl

--  F2Nat is bijection so FMap YonedaFunctor also ( using functional extensionality )

--  Full embedding of Yoneda Functor requires injective on Object, 
--
-- But we cannot prove like this
--     FObj YonedaFunctor a   ≡ FObj YonedaFunctor b → a  ≡ b
--     YondaLemma2 : {a b x : Obj A }  → (FObj (FObj YonedaFunctor a) x)  ≡ (FObj (FObj YonedaFunctor b  ) x)  →     
--         a ≡ b 
--     YondaLemma2 {a} {b} eq  = {!!}
--       N.B     = ≡-cong gives you ! a ≡ b, so we cannot cong inv to prove a ≡ b
--
-- Instead we prove only
--     inv ( FObj YonedaFunctor a )  ≡ a

inv :  {a x : Obj A} ( f : FObj (FObj YonedaFunctor a) x)  →  Obj A
inv {a} f =  Category.cod A f

YonedaLemma21 :  {a x : Obj A} ( f : ( FObj (FObj YonedaFunctor a) x) ) →  inv f  ≡ a
YonedaLemma21 {a} {x} f = refl

