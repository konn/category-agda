module HomReasoning  where 

-- Shinji KONO <kono@ie.u-ryukyu.ac.jp>

open import Category -- https://github.com/konn/category-agda
open import Level
open Functor

-- Natural Transformations
--
--        F(f)
--   F(a) ---→ F(b)
--    |          |
--    |t(a)      |t(b)    G(f)t(a) = t(b)F(f)
--    |          |
--    v          v
--   G(a) ---→ G(b)
--        G(f)

record IsNTrans {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (D : Category c₁ c₂ ℓ) (C : Category c₁′ c₂′ ℓ′)
                 ( F G : Functor D C )
                 (TMap : (A : Obj D) → Hom C (FObj F A) (FObj G A))
                 : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    naturality : {a b : Obj D} {f : Hom D a b} 
      → C [ C [ (  FMap G f ) o  ( TMap a ) ]  ≈ C [ (TMap b ) o  (FMap F f)  ] ]

record NTrans {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} (domain : Category c₁ c₂ ℓ) (codomain : Category c₁′ c₂′ ℓ′) (F G : Functor domain codomain )
       : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
  field
    TMap :  (A : Obj domain) → Hom codomain (FObj F A) (FObj G A)
    isNTrans : IsNTrans domain codomain F G TMap

module ≈-Reasoning {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) where
  open import Relation.Binary.Core 

  _o_ :  {a b c : Obj A } ( x : Hom A a b ) ( y : Hom A c a ) → Hom A c b
  x o y = A [ x o y ]

  _≈_ :  {a b : Obj A }   → Rel (Hom A a b) ℓ
  x ≈ y = A [ x ≈ y ]

  infixr 9 _o_
  infix  4 _≈_

  refl-hom :   {a b : Obj A } { x : Hom A a b }  →  x ≈ x 
  refl-hom =  IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory A ))

  trans-hom :   {a b : Obj A } { x y z : Hom A a b }  →
         x ≈ y →  y ≈ z  →  x ≈ z 
  trans-hom b c = ( IsEquivalence.trans (IsCategory.isEquivalence  ( Category.isCategory A ))) b c

  -- some short cuts

  car : {a b c : Obj A } {x y : Hom A a b } { f : Hom A c a } →
          x ≈ y  → ( x o f ) ≈ ( y  o f )
  car {f} eq = ( IsCategory.o-resp-≈ ( Category.isCategory A )) ( refl-hom  ) eq

  cdr : {a b c : Obj A } {x y : Hom A a b } { f : Hom A b c } →
          x ≈ y  →  f o x  ≈  f  o y 
  cdr {f} eq = ( IsCategory.o-resp-≈ ( Category.isCategory A )) eq (refl-hom  ) 

  id :  (a  : Obj A ) →  Hom A a a
  id a =  (Id {_} {_} {_} {A} a) 

  idL :  {a b : Obj A } { f : Hom A b a } →  id a o f  ≈ f 
  idL =  IsCategory.identityL (Category.isCategory A)

  idR :  {a b : Obj A } { f : Hom A a b } →  f o id a  ≈ f 
  idR =  IsCategory.identityR (Category.isCategory A)

  sym :  {a b : Obj A } { f g : Hom A a b } →  f ≈ g  →  g ≈ f
  sym   =  IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory A))

  assoc :   {a b c d : Obj A }  {f : Hom A c d}  {g : Hom A b c} {h : Hom A a b}
                                  →  f o ( g o h )  ≈ ( f o g ) o h
  assoc =  IsCategory.associative (Category.isCategory A)

  distr :  (T : Functor A A) →  {a b c : Obj A} {g : Hom A b c} { f : Hom A a b }
     →   FMap T ( g o f  )  ≈  FMap T g o FMap T f 
  distr T = IsFunctor.distr ( isFunctor T )

  open NTrans 
  nat : { c₁′ c₂′ ℓ′ : Level}  (D : Category c₁′ c₂′ ℓ′) {a b : Obj D} {f : Hom D a b}  {F G : Functor D A }
      →  (η : NTrans D A F G )
      →   FMap G f  o  TMap η a   ≈ TMap η b  o  FMap F f
  nat _ η  =  IsNTrans.naturality ( isNTrans η  )


  infixr  2 _∎
  infixr 2 _≈⟨_⟩_ _≈⟨⟩_ 
  infix  1 begin_

------ If we have this, for example, as an axiom of a category, we can use ≡-Reasoning directly
--  ≈-to-≡ : {a b : Obj A } { x y : Hom A a b }  → A [ x ≈  y ] → x ≡ y
--  ≈-to-≡ refl-hom = refl

  data _IsRelatedTo_ { a b : Obj A } ( x y : Hom A a b ) :
                     Set (suc (c₁ ⊔ c₂ ⊔ ℓ ))  where
      relTo : (x≈y : x ≈ y ) → x IsRelatedTo y

  begin_ : { a b : Obj A } { x y : Hom A a b } →
           x IsRelatedTo y → x ≈ y 
  begin relTo x≈y = x≈y

  _≈⟨_⟩_ : { a b : Obj A } ( x : Hom A a b ) → { y z : Hom A a b } → 
           x ≈ y → y IsRelatedTo z → x IsRelatedTo z
  _ ≈⟨ x≈y ⟩ relTo y≈z = relTo (trans-hom x≈y y≈z)

  _≈⟨⟩_ : { a b : Obj A } ( x : Hom A a b ) → { y : Hom A a b } → x IsRelatedTo y → x IsRelatedTo y
  _ ≈⟨⟩ x∼y = x∼y

  _∎ : { a b : Obj A } ( x : Hom A a b ) → x IsRelatedTo x
  _∎ _ = relTo refl-hom


-- an example

Lemma61 : {c₁ c₂ ℓ : Level} (A : Category c₁ c₂ ℓ) →
                 { a : Obj A } ( b : Obj A ) →
                 ( f : Hom A a b )
                      →  A [ A [ (Id {_} {_} {_} {A} b) o f ]  ≈ f ]
Lemma61 c b g = -- IsCategory.identityL (Category.isCategory c) 
  let open ≈-Reasoning (c) in 
     begin  
          c [ Id {_} {_} {_} {c} b o g ]
     ≈⟨ IsCategory.identityL (Category.isCategory c) ⟩
          g
     ∎


