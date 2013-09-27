-- Pullback from product and equalizer
--
--
--                        Shinji KONO <kono@ie.u-ryukyu.ac.jp>
----

open import Category -- https://github.com/konn/category-agda
open import Level
module pullback { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ') ( Γ : Functor I A ) where

open import HomReasoning
open import cat-utility

--
-- Pullback from equalizer and product
--         f
--     a -------> c
--     ^          ^
--  π1 |          |g
--     |          |
--    ab -------> b
--     ^   π2
--     |
--     | e = equalizer (f π1) (g π1)
--     |
--     d <------------------ d'
--         k (π1' × π2' )

open Equalizer
open Product
open Pullback

pullback-from :  (a b c ab d : Obj A)
      ( f : Hom A a c )    ( g : Hom A b c )
      ( π1 : Hom A ab a )  ( π2 : Hom A ab b ) ( e : Hom A d ab )
      ( eqa : {a b c : Obj A} → (f g : Hom A a b)  → {e : Hom A c a }  → Equalizer A e f g )
      ( prod : Product A a b ab π1 π2 ) → Pullback A a b c d f g
          ( A [  π1 o equalizer ( eqa ( A [ f  o π1 ] ) ( A [ g  o π2 ] ){e} )  ] )
          ( A [  π2 o equalizer ( eqa ( A [ f  o π1 ] ) ( A [ g  o π2 ] ){e} )  ] )
pullback-from  a b c ab d f g π1 π2 e eqa prod =  record {
              commute = commute1 ;
              p = p1 ;
              π1p=π1 = λ {d} {π1'} {π2'} {eq} → π1p=π11  {d} {π1'} {π2'} {eq} ;
              π2p=π2 = λ {d} {π1'} {π2'} {eq} → π2p=π21  {d} {π1'} {π2'} {eq} ;
              uniqueness = uniqueness1
      } where
      commute1 :  A [ A [ f o A [ π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] ] ≈ A [ g o A [ π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] ] ]
      commute1 = let open ≈-Reasoning (A) in
             begin
                    f o ( π1 o equalizer (eqa ( f o π1 ) ( g o π2 )) )
             ≈⟨ assoc ⟩
                    ( f o  π1 ) o equalizer (eqa ( f o π1 ) ( g o π2 ))
             ≈⟨ fe=ge (eqa (A [ f o π1 ]) (A [ g o π2 ])) ⟩
                    ( g o  π2 ) o equalizer (eqa ( f o π1 ) ( g o π2 ))
             ≈↑⟨ assoc ⟩
                    g o ( π2 o equalizer (eqa ( f o π1 ) ( g o π2 )) )
             ∎
      lemma1 :  {d' : Obj A} {π1' : Hom A d' a} {π2' : Hom A d' b} → A [ A [ f o π1' ] ≈ A [ g o π2' ] ] →
                      A [ A [ A [ f o π1 ] o (prod × π1') π2' ] ≈ A [ A [ g o π2 ] o (prod × π1') π2' ] ]
      lemma1  {d'} { π1' } { π2' } eq  = let open ≈-Reasoning (A) in
             begin
                    ( f o π1 ) o (prod × π1') π2'
             ≈↑⟨ assoc ⟩
                     f o ( π1  o (prod × π1') π2' )
             ≈⟨ cdr (π1fxg=f prod)  ⟩
                     f o  π1'
             ≈⟨ eq ⟩
                     g o  π2'
             ≈↑⟨ cdr (π2fxg=g prod)  ⟩
                     g o ( π2  o (prod × π1') π2'  )
             ≈⟨ assoc ⟩
                    ( g o π2 ) o (prod × π1') π2'
             ∎
      p1 :  {d' : Obj A} {π1' : Hom A d' a} {π2' : Hom A d' b} → A [ A [ f o π1' ] ≈ A [ g o π2' ] ] → Hom A d' d
      p1 {d'} { π1' } { π2' } eq  =
         let open ≈-Reasoning (A) in k ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e} ) (_×_ prod  π1'  π2' ) ( lemma1 eq )
      π1p=π11 :   {d₁ : Obj A} {π1' : Hom A d₁ a} {π2' : Hom A d₁ b} {eq : A [ A [ f o π1' ] ≈ A [ g o π2' ] ]} →
            A [ A [ A [ π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]) {e} ) ] o p1 eq ] ≈ π1' ]
      π1p=π11 {d'} {π1'} {π2'} {eq} = let open ≈-Reasoning (A) in
             begin
                     ( π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]) {e} ) ) o p1 eq
             ≈⟨⟩
                     ( π1 o e) o  k ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e} ) (_×_ prod  π1'  π2' ) (lemma1 eq)
             ≈↑⟨ assoc ⟩
                      π1 o ( e o  k ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e} ) (_×_ prod  π1'  π2' ) (lemma1 eq) )
             ≈⟨ cdr ( ek=h  ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e} )) ⟩
                      π1 o  (_×_ prod  π1'  π2' )
             ≈⟨ π1fxg=f prod ⟩
                     π1'
             ∎
      π2p=π21 : {d₁ : Obj A} {π1' : Hom A d₁ a} {π2' : Hom A d₁ b} {eq : A [ A [ f o π1' ] ≈ A [ g o π2' ] ]} →
            A [ A [ A [ π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]) {e} ) ] o p1 eq ] ≈ π2' ]
      π2p=π21  {d'} {π1'} {π2'} {eq} = let open ≈-Reasoning (A) in
             begin
                     ( π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ]) {e} ) ) o p1 eq
             ≈⟨⟩
                     ( π2 o e) o  k ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e} ) (_×_ prod  π1'  π2' ) (lemma1 eq)
             ≈↑⟨ assoc ⟩
                      π2 o ( e o  k ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e} ) (_×_ prod  π1'  π2' ) (lemma1 eq) )
             ≈⟨ cdr ( ek=h  ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e} )) ⟩
                      π2 o  (_×_ prod  π1'  π2' )
             ≈⟨ π2fxg=g prod ⟩
                     π2'
             ∎
      uniqueness1 :  {d₁ : Obj A} (p' : Hom A d₁ d) {π1' : Hom A d₁ a} {π2' : Hom A d₁ b} {eq : A [ A [ f o π1' ] ≈ A [ g o π2' ] ]} →
        {eq1 : A [ A [ A [ π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] o p' ] ≈ π1' ]} →
        {eq2 : A [ A [ A [ π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] o p' ] ≈ π2' ]} →
        A [ p1 eq ≈ p' ]
      uniqueness1 {d'} p' {π1'} {π2'} {eq} {eq1} {eq2} = let open ≈-Reasoning (A) in
             begin
                 p1 eq
             ≈⟨⟩
                 k ( eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e} ) (_×_ prod  π1'  π2' ) (lemma1 eq)
             ≈⟨ Equalizer.uniqueness (eqa ( A [ f o π1 ] ) ( A [ g o π2 ] ) {e}) ( begin
                 e o p'
             ≈⟨⟩
                  equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) o p'
             ≈↑⟨ Product.uniqueness prod ⟩
                (prod × (  π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) o p') ) ( π2 o (equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) o p'))
             ≈⟨ ×-cong prod (assoc) (assoc) ⟩
                 (prod × (A [ A [ π1 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] o p' ]))
                         (A [ A [ π2 o equalizer (eqa (A [ f o π1 ]) (A [ g o π2 ])) ] o p' ])
             ≈⟨ ×-cong prod eq1 eq2 ⟩
                ((prod × π1') π2')
             ∎ ) ⟩
                 p'
             ∎

------
--
-- Limit
--
-----

-- Constancy Functor

K : { c₁' c₂' ℓ' : Level}  (A : Category c₁' c₂' ℓ') { c₁'' c₂'' ℓ'' : Level} ( I : Category c₁'' c₂'' ℓ'' ) 
    → ( a : Obj A ) → Functor I A
K A I a = record {
      FObj = λ i → a ;
      FMap = λ f → id1 A a ;
        isFunctor = let  open ≈-Reasoning (A) in record {
               ≈-cong   = λ f=g → refl-hom
             ; identity = refl-hom
             ; distr    = sym idL
        }
  }

open NTrans

record Limit { c₁' c₂' ℓ' : Level} { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ ) ( I : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
     ( a0 : Obj A ) (  t0 : NTrans I A ( K A I a0 ) Γ ) : Set (suc (c₁' ⊔ c₂' ⊔ ℓ' ⊔ c₁ ⊔ c₂ ⊔ ℓ )) where
  field
     limit :  ( a : Obj A ) → ( t : NTrans I A ( K A I a ) Γ ) → Hom A a a0
     t0f=t :  { a : Obj A } → { t : NTrans I A ( K A I a ) Γ } → ∀ { i : Obj I } →
         A [ A [ TMap t0 i o  limit a t ]  ≈ TMap t i ]
     limit-uniqueness : { a : Obj A } →  { t : NTrans I A ( K A I a ) Γ } → { f : Hom A a a0 } → ( ∀ { i : Obj I } →
         A [ A [ TMap t0 i o  f ]  ≈ TMap t i ] ) → A [ limit a t ≈ f ]
  A0 : Obj A
  A0 = a0
  T0 : NTrans I A ( K A I a0 ) Γ
  T0 = t0

--------------------------------
--
-- If we have two limits on c and c', there are isomorphic pair h, h'

open Limit

iso-l :  { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
     ( a0 a0' : Obj A ) (  t0 : NTrans I A ( K A I a0 ) Γ ) (  t0' : NTrans I A ( K A I a0' ) Γ )
       ( lim : Limit A I Γ a0 t0 ) → ( lim' :  Limit A I Γ a0' t0' )
      → Hom A a0 a0'
iso-l  I Γ a0 a0' t0 t0' lim lim' = limit lim' a0 t0

iso-r :  { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
     ( a0 a0' : Obj A ) (  t0 : NTrans I A ( K A I a0 ) Γ ) (  t0' : NTrans I A ( K A I a0' ) Γ )
       ( lim : Limit A I Γ a0 t0 ) → ( lim' :  Limit A I Γ a0' t0' )
      → Hom A a0' a0
iso-r  I Γ a0 a0' t0 t0' lim lim' = limit lim a0' t0'


iso-lr :  { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ' ) ( Γ : Functor I A )
     ( a0 a0' : Obj A ) (  t0 : NTrans I A ( K A I a0 ) Γ ) (  t0' : NTrans I A ( K A I a0' ) Γ )
       ( lim : Limit A I Γ a0 t0 ) → ( lim' :  Limit A I Γ a0' t0' )  → ∀{ i : Obj I } →
  A [ A [ iso-l I Γ a0 a0' t0 t0' lim lim' o iso-r I Γ a0 a0' t0 t0' lim lim'  ]  ≈ id1 A a0' ]
iso-lr  I Γ a0 a0' t0 t0' lim lim' {i} =  let open ≈-Reasoning (A) in begin
           limit lim' a0 t0 o limit lim a0' t0'
      ≈↑⟨ limit-uniqueness lim'  ( λ {i} → ( begin
          TMap t0' i o ( limit lim' a0 t0 o limit lim a0' t0' )
      ≈⟨ assoc  ⟩
          ( TMap t0' i o  limit lim' a0 t0 ) o limit lim a0' t0'
      ≈⟨ car ( t0f=t lim' ) ⟩
          TMap t0 i o limit lim a0' t0'
      ≈⟨ t0f=t lim ⟩
          TMap t0' i
      ∎) ) ⟩
           limit lim' a0' t0'
      ≈⟨ limit-uniqueness lim' idR ⟩
           id a0'
      ∎


open import CatExponetial

open Functor

--------------------------------
--
-- Contancy Functor

KI : { c₁' c₂' ℓ' : Level} ( I : Category c₁' c₂' ℓ' ) →  Functor A ( A ^ I )
KI { c₁'} {c₂'} {ℓ'} I = record {
      FObj = λ a → K A I a ;
      FMap = λ f → record { --  NTrans I A (K A I a)  (K A I b)
            TMap = λ a → f ;
            isNTrans = record {
                 commute = λ {a b f₁} → commute1 {a} {b} {f₁} f
            }
        }  ;
        isFunctor = let  open ≈-Reasoning (A) in record {
               ≈-cong   = λ f=g {x} → f=g
             ; identity = refl-hom
             ; distr    = refl-hom
        }
  } where
     commute1 :  {a b : Obj I} {f₁ : Hom I a b} → {a' b' : Obj A} → (f : Hom A a' b' ) →
        A [ A [ FMap (K A I b') f₁ o f ] ≈ A [ f o FMap (K A I a') f₁ ] ]
     commute1 {a} {b} {f₁} {a'} {b'} f = let  open ≈-Reasoning (A) in begin
            FMap (K A I b') f₁ o f
        ≈⟨ idL ⟩
           f
        ≈↑⟨ idR ⟩
            f o FMap (K A I a') f₁
        ∎


---------
--
--   Limit    Constancy Functor F : A → A^I     has right adjoint
--
--   we are going to prove universal mapping

---------
--
-- limit gives co universal mapping ( i.e. adjunction )
--
--     F = KI I : Functor A (A ^ I)
--     U = λ b → A0 (lim b {a0 b} {t0 b}
--     ε = λ b → T0 ( lim b {a0 b} {t0 b} )

limit2couniv :
     ( lim : ( Γ : Functor I A ) → { a0 : Obj A } { t0 : NTrans I A ( K A I a0 ) Γ } → Limit A I Γ a0 t0 )
     → ( a0 : ( b : Functor I A ) → Obj A ) ( t0 :  ( b : Functor I A ) → NTrans I A ( K A I (a0 b) ) b )
     →  coUniversalMapping A ( A ^ I ) (KI I) (λ b → A0 (lim b {a0 b} {t0 b} ) )  ( λ b → T0 ( lim b {a0 b} {t0 b} ) )
limit2couniv lim a0 t0 = record {  -- F             U                            ε
       _*' = λ {b} {a} k → limit (lim b {a0 b} {t0 b} ) a k ; -- η
       iscoUniversalMapping = record {
           couniversalMapping = λ{ b a f} → couniversalMapping1 {b} {a} {f} ;
           couniquness = couniquness2
       }
  } where
   couniversalMapping1 :  {b : Obj (A ^ I)} {a : Obj A} {f : Hom (A ^ I) (FObj (KI I) a) b} →
        A ^ I [ A ^ I [ T0 (lim b {a0 b} {t0 b}) o FMap (KI I) (limit (lim b {a0 b} {t0 b}) a f) ] ≈ f ]
   couniversalMapping1 {b} {a} {f} {i} = let  open ≈-Reasoning (A) in begin
            TMap (T0 (lim b {a0 b} {t0 b})) i o TMap ( FMap (KI I) (limit (lim b {a0 b} {t0 b}) a f) ) i
        ≈⟨⟩
            TMap (t0 b) i o (limit (lim b) a f)
        ≈⟨ t0f=t (lim b) ⟩
            TMap f i  -- i comes from   ∀{i} → B [ TMap f i  ≈  TMap g i  ]
        ∎
   couniquness2 : {b : Obj (A ^ I)} {a : Obj A} {f : Hom (A ^ I) (FObj (KI I) a) b} {g : Hom A a (A0 (lim b {a0 b} {t0 b} ))} →
        ( ∀ { i : Obj I } → A [ A [ TMap (T0 (lim b {a0 b} {t0 b} )) i  o TMap ( FMap (KI I) g) i  ] ≈ TMap f i ] )
         → A [ limit (lim b {a0 b} {t0 b} ) a f ≈ g ]
   couniquness2 {b} {a} {f} {g} lim-g=f  =  let  open ≈-Reasoning (A) in begin
            limit (lim b {a0 b} {t0 b} ) a f
        ≈⟨ limit-uniqueness ( lim b {a0 b} {t0 b} ) lim-g=f ⟩
            g
        ∎

open import Category.Cat


open coUniversalMapping

univ2limit :
     ( U : Obj (A ^ I ) → Obj A )
     ( ε : ( b : Obj (A ^ I ) ) → NTrans I A (K A I (U b)) b )
     ( univ :  coUniversalMapping A (A ^ I) (KI I) U (ε) ) →
     ( Γ : Functor I A ) →   Limit A I Γ (U Γ) (ε Γ)
univ2limit U ε univ Γ = record {
     limit = λ a t → limit1 a t ;
     t0f=t = λ {a t i } → t0f=t1 {a} {t} {i}  ;
     limit-uniqueness =  λ {a} {t} {f} t=f → limit-uniqueness1 {a} {t} {f} t=f
 } where
     limit1 :  (a : Obj A) → NTrans I A (K A I a) Γ → Hom A a (U Γ)
     limit1 a t = _*' univ {_} {a} t
     t0f=t1 :   {a : Obj A} {t : NTrans I A (K A I a) Γ}  {i : Obj I} →
                A [ A [ TMap (ε Γ) i o limit1 a t ] ≈ TMap t i ]
     t0f=t1 {a} {t} {i} =  let  open ≈-Reasoning (A) in begin
            TMap (ε Γ) i o limit1 a t
        ≈⟨⟩
            TMap (ε Γ) i o _*' univ {Γ} {a} t
        ≈⟨ coIsUniversalMapping.couniversalMapping ( iscoUniversalMapping univ) {Γ} {a} {t} ⟩
            TMap t i
        ∎
     limit-uniqueness1 : { a : Obj A } →  { t : NTrans I A ( K A I a ) Γ } → { f : Hom A a (U Γ)}
         → ( ∀ { i : Obj I } → A [ A [ TMap  (ε Γ) i o  f ]  ≈ TMap t i ] ) → A [ limit1 a t ≈ f ]
     limit-uniqueness1 {a} {t} {f} εf=t = let  open ≈-Reasoning (A) in begin
            _*' univ t
        ≈⟨  ( coIsUniversalMapping.couniquness ( iscoUniversalMapping univ) ) εf=t  ⟩
            f
        ∎

-----
--
-- product on arbitrary index
--

record IProduct { c c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  ( I : Set c)
      ( p  : Obj A )                       -- product
      ( ai : I → Obj A )                   -- families
      ( pi : (i : I ) → Hom A p ( ai i ) ) -- projections
            : Set  (c ⊔ ℓ ⊔ (c₁ ⊔ c₂)) where
   field
      product : {q : Obj A}  → ( qi : (i : I) → Hom A q (ai i) ) → Hom A q p
      pif=q :   {q : Obj A}  → ( qi : (i : I) → Hom A q (ai i) ) → ∀ { i : I } → A [ A [ ( pi i )  o ( product qi ) ] ≈  (qi i) ]
      -- special case of product ( qi = pi ) ( should b proved from pif=q )
      --   we cannot prove this because qi/pi cannot be interleaved , should be the way to prove
      pif=q1 :   { i : I } → { qi :  Hom A p (ai i) } → A [ pi i ≈  qi ]
      ip-uniqueness :  {q : Obj A} { h : Hom A q p } → A [ product ( λ (i : I) →  A [ (pi i)  o h ] )  ≈  h ]
      ip-cong : {q : Obj A}   → { qi : (i : I) → Hom A q (ai i) } → { qi' : (i : I) → Hom A q (ai i) }
                → ( ∀ (i : I ) →  A [ qi i ≈ qi' i ] ) → A [ product qi ≈ product qi' ]
      ip-uniquness1 : {q : Obj A}  → ( qi : (i : I) → Hom A q (ai i) ) → ∀ { i : I }  → ( product' : Hom A q p ) 
          → A [ A [ ( pi i )  o product' ] ≈  (qi i) ]
          → A [ product'  ≈ product qi ]

open IProduct
open Equalizer

--
-- limit from equalizer and product
--
--      
--        ai 
--        ^                                       K f = id lim
--        | pi                          lim = K i ------------> K j = lim
--        |                                     |               |
--        p                                     |               |
--        ^                                 ε i |               | ε j
--        |                                     |               |
--        | e = equalizer (id p) (id p)         |               |
--        |                                     v               v
--       lim <------------------ d'     a i = Γ i ------------> Γ j = a j
--         k ( product pi )                          Γ f
--                                              Γ f o ε i = ε j 
--
--

-- pi-ε -- : ( prod : (p : Obj A) ( ai : Obj I → Obj A )  ( pi : (i : Obj I) → Hom A p ( ai i ) )
--                   →  IProduct {c₁'} A (Obj I) p ai pi )
--      ( lim p : Obj A ) ( e : Hom  A lim p )
--      ( proj : (i : Obj I ) → Hom A p (FObj Γ i) ) →
--      { i : Obj I } → { q :  ( i : Obj I )  → Hom A p (FObj Γ i) } → A [ proj i ≈  q i ]
-- pi-ε prod lim p e proj {i} {q} = let  open ≈-Reasoning (A) in begin
--            proj i 
--         ≈↑⟨ idR ⟩
--            proj i o id1 A p
--         ≈⟨ cdr {!!} ⟩
--            proj i o product (prod p (FObj Γ) proj) q
--         ≈⟨ pif=q (prod p (FObj Γ) proj)  q ⟩
--            q i
--         ∎


limit-ε :
      ( prod : (p : Obj A) ( ai : Obj I → Obj A )  ( pi : (i : Obj I) → Hom A p ( ai i ) )
                  →  IProduct {c₁'} A (Obj I) p ai pi )
     ( lim p : Obj A ) ( e : Hom  A lim p )
     ( proj : (i : Obj I ) → Hom A p (FObj Γ i) ) →
         NTrans I A (K A I lim) Γ
limit-ε prod lim p e proj = record {
      TMap = tmap ;
      isNTrans = record {
          commute = commute1 
      }
  } where
      tmap : (i : Obj I) → Hom A (FObj (K A I lim) i) (FObj Γ i)
      tmap i = A [ proj i o e ]
      commute1 :  {i j : Obj I} {f : Hom I i j} →
        A [ A [ FMap Γ f o tmap i ] ≈ A [ tmap j o FMap (K A I lim) f ] ]
      commute1 {i} {j} {f} =  let  open ≈-Reasoning (A) in begin
             FMap Γ f o tmap i 
        ≈⟨⟩
             FMap Γ f o ( proj i o e )
        ≈⟨ assoc ⟩
             ( FMap Γ f o  proj i ) o e 
        ≈↑⟨ car ( pif=q1 ( prod p (FObj Γ)  proj ) {j} ) ⟩
             proj j o e 
        ≈↑⟨ idR ⟩
             (proj j o e ) o id1 A lim
        ≈⟨⟩
             tmap j o FMap (K A I lim) f
        ∎  

limit-from :
     ( prod : (p : Obj A) ( ai : Obj I → Obj A )  ( pi : (i : Obj I) → Hom A p ( ai i ) )
                  →  IProduct {c₁'} A (Obj I) p ai pi )
     ( eqa : {a b c : Obj A} → (e : Hom A c a )  → (f g : Hom A a b)  → Equalizer A e f g )
     ( lim p : Obj A )       -- limit to be made
     ( e : Hom  A lim p )                          -- existing of equalizer
     ( proj : (i : Obj I ) → Hom A p (FObj Γ i) )  -- existing of product ( projection actually )
      → Limit A I Γ lim ( limit-ε prod lim p e proj )
limit-from prod eqa lim p e proj = record {
     limit = λ a t → limit1 a t ;
     t0f=t = λ {a t i } → t0f=t1 {a} {t} {i}  ;
     limit-uniqueness =  λ {a} {t} {f} t=f → limit-uniqueness1 {a} {t} {f} t=f
    }  where
         limit1 :  (a : Obj A) → NTrans I A (K A I a) Γ → Hom A a lim
         limit1 a t = let  open ≈-Reasoning (A) in k (eqa e (id1 A p) (id1 A p )) (product ( prod p (FObj Γ)  proj ) (TMap t) ) refl-hom
         t0f=t1 :  {a : Obj A} {t : NTrans I A (K A I a) Γ} {i : Obj I} →
                A [ A [ TMap (limit-ε prod lim p e proj ) i o limit1 a t ] ≈ TMap t i ]
         t0f=t1 {a} {t} {i} = let  open ≈-Reasoning (A) in begin
                   TMap (limit-ε prod lim p e proj ) i o limit1 a t 
                ≈⟨⟩
                   ( ( proj i )  o e ) o  k (eqa e (id1 A p) (id1 A p )) (product ( prod p (FObj Γ)  proj ) (TMap t) ) refl-hom
                ≈↑⟨ assoc  ⟩
                    proj i  o ( e  o  k (eqa e (id1 A p) (id1 A p )) (product ( prod p (FObj Γ)  proj ) (TMap t) ) refl-hom )
                ≈⟨ cdr ( ek=h ( eqa e (id1 A p) (id1 A p ) ) ) ⟩
                    proj i  o product (prod p (FObj Γ) proj) (TMap t)
                ≈⟨ pif=q (prod p (FObj Γ) proj) (TMap t) ⟩
                   TMap t i 
                ∎
         limit-uniqueness1 :  {a : Obj A} {t : NTrans I A (K A I a) Γ} {f : Hom A a lim} 
                → ({i : Obj I} → A [ A [ TMap (limit-ε prod lim p e proj ) i o f ] ≈ TMap t i ]) →
                A [ limit1 a t ≈ f ]
         limit-uniqueness1 {a} {t} {f} lim=t = let  open ≈-Reasoning (A) in begin
                    limit1 a t
                ≈⟨⟩
                    k (eqa e (id1 A p) (id1 A p )) (product ( prod p (FObj Γ)  proj ) (TMap t) ) refl-hom
                ≈⟨ Equalizer.uniqueness  (eqa e (id1 A p) (id1 A p )) ( begin
                      e o f 
                ≈↑⟨ ip-uniqueness (prod p (FObj Γ) proj) ⟩
                      product (prod p (FObj Γ) proj) (λ i → ( proj i o ( e  o f ) ) )
                ≈⟨ ip-cong  (prod p (FObj Γ) proj) ( λ i → begin
                        proj i o ( e o f )
                ≈⟨ assoc  ⟩
                        ( proj i o  e ) o f 
                ≈⟨ lim=t {i} ⟩
                        TMap t i
                ∎ ) ⟩
                      product (prod p (FObj Γ) proj) (TMap t)
                ∎ ) ⟩
                    f
                ∎

----
--
-- Adjoint functor preserves limits
--
--      

open import Category.Cat

ta1 : { c₁' c₂' ℓ' : Level}  (B : Category c₁' c₂' ℓ') ( Γ : Functor I B ) 
     ( lim : Obj B ) ( tb : NTrans I B ( K B I lim ) Γ ) → 
         ( U : Functor B A)  → NTrans I A ( K A I (FObj U lim) ) (U  ○  Γ)
ta1 B Γ lim tb U = record {
               TMap  = TMap (Functor*Nat I A U tb) ; 
               isNTrans = record { commute = λ {a} {b} {f} → let  open ≈-Reasoning (A) in begin
                     FMap (U ○ Γ) f o TMap (Functor*Nat I A U tb) a 
                 ≈⟨ nat ( Functor*Nat I A U tb ) ⟩
                     TMap (Functor*Nat I A U tb) b o FMap (U ○ K B I lim) f 
                 ≈⟨ cdr (IsFunctor.identity (isFunctor U) ) ⟩
                     TMap (Functor*Nat I A U tb) b o FMap (K A I (FObj U lim)) f
                 ∎
               } }
 
adjoint-preseve-limit :
     { c₁' c₂' ℓ' : Level}  (B : Category c₁' c₂' ℓ') ( Γ : Functor I B ) 
     ( lim : Obj B ) ( tb : NTrans I B ( K B I lim ) Γ ) → ( limitb : Limit B I Γ lim tb ) →
         { U : Functor B A } { F : Functor A B }
         { η : NTrans A A identityFunctor ( U ○ F ) }
         { ε : NTrans B B  ( F ○  U ) identityFunctor } →
       ( adj : Adjunction A B U F η ε  ) →  Limit A I (U ○ Γ) (FObj U lim) (ta1 B Γ lim tb U ) 
adjoint-preseve-limit B Γ lim tb limitb {U} {F} {η} {ε} adj = record {
     limit = λ a t → limit1 a t ;
     t0f=t = λ {a t i } → t0f=t1 {a} {t} {i}  ;
     limit-uniqueness =  λ {a} {t} {f} t=f → limit-uniqueness1 {a} {t} {f} t=f
    } where
         ta = ta1 B Γ lim tb U
         tfmap : (a : Obj A) → NTrans I A (K A I a) (U ○ Γ) → (i : Obj I) → Hom B (FObj (K B I (FObj F a)) i) (FObj Γ i)
         tfmap a t i  = B [ TMap ε (FObj Γ i) o FMap F (TMap t i) ]
         tF :  (a : Obj A) → NTrans I A (K A I a) (U ○ Γ) →  NTrans I B (K B I (FObj F a)) Γ
         tF a t = record {
             TMap = tfmap a t ; 
             isNTrans = record { commute = λ {a'} {b} {f} → let  open ≈-Reasoning (B) in begin
                  FMap Γ f o tfmap a t a' 
               ≈⟨⟩
                  FMap Γ f o ( TMap ε (FObj Γ a') o FMap F (TMap t a'))
               ≈⟨ assoc ⟩
                  (FMap Γ f o  TMap ε (FObj Γ a') ) o FMap F (TMap t a')
               ≈⟨ car (nat ε) ⟩
                  (TMap ε (FObj Γ b) o FMap (F ○ U) (FMap Γ f) ) o FMap F (TMap t a')
               ≈↑⟨ assoc ⟩
                  TMap ε (FObj Γ b) o ( FMap (F ○ U) (FMap Γ f)  o FMap F (TMap t a') )
               ≈↑⟨ cdr ( distr F ) ⟩
                  TMap ε (FObj Γ b) o ( FMap F (A [ FMap U (FMap Γ f) o TMap t a' ] ) )
               ≈⟨ cdr ( fcong F (nat t) ) ⟩
                  TMap ε (FObj Γ b) o  FMap F (A [ TMap t b o FMap (K A I a) f ])
               ≈⟨⟩
                  TMap ε (FObj Γ b) o  FMap F (A [ TMap t b o id1 A (FObj (K A I a) b) ])
               ≈⟨ cdr ( fcong F (idR1 A)) ⟩
                  TMap ε (FObj Γ b) o  FMap F (TMap t b )
               ≈↑⟨ idR ⟩
                  ( TMap ε (FObj Γ b)  o  FMap F (TMap t b))  o  id1 B (FObj F (FObj (K A I a) b))
               ≈⟨⟩
                  tfmap a t b o FMap (K B I (FObj F a)) f 
               ∎
          } }
         limit1 :  (a : Obj A) → NTrans I A (K A I a) (U ○ Γ) → Hom A a (FObj U lim)
         limit1 a t = A [ FMap U (limit limitb (FObj F a) (tF a t )) o TMap η a ]
         t0f=t1 :  {a : Obj A} {t : NTrans I A (K A I a) (U ○ Γ)} {i : Obj I} →
                A [ A [ TMap ta i o limit1 a t ] ≈ TMap t i ]
         t0f=t1 {a} {t} {i} = let  open ≈-Reasoning (A) in  begin
                 TMap ta i o limit1 a t 
               ≈⟨⟩
                  FMap U ( TMap tb i )  o ( FMap U (limit limitb (FObj F a) (tF a t )) o TMap η a  )
               ≈⟨ assoc ⟩
                  ( FMap U ( TMap tb i )  o  FMap U (limit limitb (FObj F a) (tF a t ))) o TMap η a  
               ≈↑⟨ car ( distr U ) ⟩
                  FMap U ( B [ TMap tb i  o limit limitb (FObj F a) (tF a t ) ] ) o TMap η a  
               ≈⟨ car ( fcong U ( t0f=t limitb ) ) ⟩
                  FMap U (TMap (tF a t) i) o TMap η a  
               ≈⟨⟩
                  FMap U ( B [ TMap ε (FObj Γ i) o FMap F (TMap t i) ] ) o TMap η a  
               ≈⟨ car ( distr U ) ⟩
                  ( FMap U ( TMap ε (FObj Γ i))  o FMap U ( FMap F (TMap t i) )) o TMap η a  
               ≈↑⟨ assoc ⟩
                   FMap U ( TMap ε (FObj Γ i) ) o ( FMap U ( FMap F (TMap t i) ) o TMap η a   )
               ≈⟨ cdr ( nat η ) ⟩
                    FMap U (TMap ε (FObj Γ i)) o (  TMap η (FObj U (FObj Γ i)) o FMap (identityFunctor {_} {_} {_} {A}) (TMap t i) )
               ≈⟨ assoc ⟩
                    ( FMap U (TMap ε (FObj Γ i)) o   TMap η (FObj U (FObj Γ i))) o TMap t i
               ≈⟨ car ( IsAdjunction.adjoint1 ( Adjunction.isAdjunction adj ) ) ⟩
                 id1 A (FObj (U ○ Γ) i) o TMap t i
               ≈⟨ idL ⟩
                 TMap t i
               ∎
         -- ta = TMap (Functor*Nat I A U tb) , FMap U ( TMap tb i )  o f  ≈ TMap t i
         limit-uniqueness1 :  {a : Obj A} {t : NTrans I A (K A I a) (U ○ Γ)} {f : Hom A a (FObj U lim)} 
                → ({i : Obj I} → A [ A [ TMap ta i o f ] ≈ TMap t i ]) →
                A [ limit1 a t ≈ f ]
         limit-uniqueness1 {a} {t} {f} lim=t = let  open ≈-Reasoning (A) in  begin
                 limit1 a t
               ≈⟨⟩
                 FMap U (limit limitb (FObj F a) (tF a t )) o TMap η a  
               ≈⟨ car ( fcong U (limit-uniqueness limitb ( λ {i} →  lemma1 i) )) ⟩
                 FMap U ( B [ TMap ε lim o FMap F f ] ) o TMap η a   -- Universal mapping 
               ≈⟨ car (distr U ) ⟩
                 ( (FMap U (TMap ε lim))  o (FMap U ( FMap F f )) ) o TMap η a
               ≈⟨ sym assoc ⟩
                  (FMap U (TMap ε lim))  o ((FMap U ( FMap F f ))  o TMap η a )
               ≈⟨ cdr (nat η) ⟩
                  (FMap U (TMap ε lim))  o ((TMap η (FObj U lim )) o f )
               ≈⟨ assoc ⟩
                  ((FMap U (TMap ε lim))  o (TMap η (FObj U lim)))  o f
               ≈⟨ car ( IsAdjunction.adjoint1 ( Adjunction.isAdjunction adj))  ⟩
                  id (FObj U lim) o f
               ≈⟨  idL  ⟩
                  f
               ∎ where
                  lemma1 : (i : Obj I) → B [ B [ TMap tb i o B [ TMap ε lim  o FMap F f ] ] ≈ TMap (tF a t) i ]
                  lemma1 i =  let  open ≈-Reasoning (B) in  begin
                          TMap tb i o (TMap ε lim  o FMap F f)
                       ≈⟨ assoc ⟩
                          ( TMap tb i o TMap ε lim  ) o FMap F f
                       ≈⟨ car ( nat ε ) ⟩
                          ( TMap ε (FObj Γ i) o  FMap F ( FMap U ( TMap tb i )))  o FMap F f 
                       ≈↑⟨ assoc  ⟩
                          TMap ε (FObj Γ i) o  ( FMap F ( FMap U ( TMap tb i ))  o FMap F f )
                       ≈↑⟨ cdr ( distr F )  ⟩
                          TMap ε (FObj Γ i) o  FMap F ( A [ FMap U ( TMap tb i )  o f ] ) 
                       ≈⟨ cdr ( fcong F (lim=t {i}) ) ⟩
                          TMap ε (FObj Γ i) o FMap F (TMap t i) 
                       ≈⟨⟩
                          TMap (tF a t) i  
                       ∎ 

     

