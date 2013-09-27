---
--
--  Equalizer
--
--         e             f
--    c  --------> a ----------> b
--    ^        .     ---------->
--    |      .            g
--    |k   .
--    |  . h
--    d
--
--                        Shinji KONO <kono@ie.u-ryukyu.ac.jp>
----

open import Category -- https://github.com/konn/category-agda
open import Level
module equalizer { c₁ c₂ ℓ : Level} { A : Category c₁ c₂ ℓ } where

open import HomReasoning
open import cat-utility

-- in cat-utility
-- record Equalizer { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {c a b : Obj A} (e : Hom A c a) (f g : Hom A a b)  : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
--    field
--       fe=ge : A [ A [ f o e ] ≈ A [ g o e ] ]
--       k : {d : Obj A}  (h : Hom A d a) → A [ A [ f  o  h ] ≈ A [ g  o h ] ] → Hom A d c
--       ek=h : {d : Obj A}  → ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  A [ A [ e  o k {d} h eq ] ≈ h ]
--       uniqueness : {d : Obj A} →  ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  {k' : Hom A d c } →
--               A [ A [ e  o k' ] ≈ h ] → A [ k {d} h eq  ≈ k' ]
--    equalizer : Hom A c a
--    equalizer = e


--
-- Burroni's Flat Equational Definition of Equalizer
--
record Burroni { c₁ c₂ ℓ : Level} ( A : Category c₁ c₂ ℓ )  {c a b : Obj A} (f g : Hom A a b) (e : Hom A c a) : Set  (ℓ ⊔ (c₁ ⊔ c₂)) where
   field
      α : {a b c : Obj A } → (f : Hom A a b) → (g : Hom A a b ) →  (e : Hom A c a ) → Hom A c a
      γ : {a b c d : Obj A } → (f : Hom A a b) → (g : Hom A a b ) → (h : Hom A d a ) →  Hom A d c
      δ : {a b c : Obj A } → (e : Hom A c a ) → (f : Hom A a b) → Hom A a c
      cong-α : {a b c :  Obj A } → { e : Hom A c a }
          → {f g g' : Hom A a b } →  A [ g ≈ g' ] → A [ α f g e ≈ α f g' e ] 
      cong-γ : {a _ c d : Obj A } → {f g : Hom A a b} {h h' : Hom A d a } →  A [ h ≈ h' ] 
         → A [ γ {a} {b} {c} {d} f g h ≈ γ f g h' ] 
      cong-δ : {a b c : Obj A } → {e : Hom A c a} → {f f' : Hom A a b} → A [ f ≈ f' ] →  A [ δ e f ≈ δ e f' ] 
      b1 : A [ A [ f  o α {a} {b} {c}  f g e ] ≈ A [ g  o α {a} {b} {c} f g e ] ]
      b2 :  {d : Obj A } → {h : Hom A d a } → A [ A [ ( α {a} {b} {c} f g e ) o (γ {a} {b} {c} f g h) ] ≈ A [ h  o α (A [ f o h ]) (A [ g o h ]) (id1 A d) ] ]
      b3 : {a b d : Obj A} → (f : Hom A a b ) → {h : Hom A d a } → A [ A [ α {a} {b} {d} f f h o δ {a} {b} {d} h f ] ≈ id1 A a ]
      -- b4 :  {c d : Obj A } {k : Hom A c a} → A [ β f g ( A [ α f g o  k ] ) ≈ k ]
      b4 :  {d : Obj A } {k : Hom A d c} → 
           A [ A [ γ {a} {b} {c} {d} f g ( A [ α {a} {b} {c} f g e o k ] ) o ( δ {d} {b} {d} (id1 A d) (A [ f o A [ α {a} {b} {c} f g e o  k ] ] )  )] ≈ k ]
   --  A [ α f g o β f g h ] ≈ h
   β : { d a b : Obj A}  → (f : Hom A a b) → (g : Hom A a b ) →  (h : Hom A d a ) → Hom A d c
   β {d} {a} {b} f g h =  A [ γ {a} {b} {c} f g h o δ {d} {b} {d} (id1 A d) (A [ f o h ]) ]

open Equalizer
open Burroni

--
-- Some obvious conditions for k  (fe = ge) → ( fh = gh )
--

f1=g1 : { a b c : Obj A } {f g : Hom A a b } → (eq : A [ f ≈ g ] ) → (h : Hom A c a) →  A [ A [ f o h ] ≈ A [ g o h ]  ]
f1=g1 eq h = let open ≈-Reasoning (A) in (resp refl-hom eq )

f1=f1 : { a b : Obj A } (f : Hom A a b ) →  A [ A [ f o (id1 A a)  ] ≈ A [ f o (id1 A a)  ]  ]
f1=f1  f = let open ≈-Reasoning (A) in refl-hom

f1=gh : { a b c d : Obj A } {f g : Hom A a b } → { e : Hom A c a } → { h : Hom A d c } →
       (eq : A [ A [ f  o e ] ≈ A [ g  o e ] ] ) → A [ A [ f o A [ e o h ] ] ≈ A [ g o A [ e  o h ]  ] ]
f1=gh {a} {b} {c} {d} {f} {g} {e} {h} eq = let open ≈-Reasoning (A) in
             begin
                  f o ( e  o h )
             ≈⟨ assoc  ⟩
                  (f o  e ) o h
             ≈⟨ car eq  ⟩
                  (g o  e ) o h
             ≈↑⟨ assoc  ⟩
                  g o ( e  o h )
             ∎

-------------------------------
-- 
-- Every equalizer is monic
--
--     e i = e j → i = j
--
--           e eqa f g        f
--         c ----------> a ------->b
--        ^^
--        ||
--       i||j
--        ||
--         d

monoic : { c a b d : Obj A } {f g : Hom A a b } → {e : Hom A c a } ( eqa : Equalizer A e f g) 
      →  { i j : Hom A d c }
      →  A [ A [ equalizer eqa o i ]  ≈  A [ equalizer eqa o j ] ] →  A [ i  ≈ j  ]
monoic {c} {a} {b} {d} {f} {g} {e} eqa {i} {j} ei=ej = let open ≈-Reasoning (A) in begin
                 i
              ≈↑⟨ uniqueness eqa ( begin
                   equalizer eqa  o i
              ≈⟨ ei=ej ⟩
                   equalizer eqa  o j
              ∎ )⟩
                 k eqa (equalizer eqa o j) ( f1=gh (fe=ge eqa ) )
              ≈⟨ uniqueness eqa ( begin
                   equalizer eqa o j
              ≈⟨⟩
                   equalizer eqa o j
              ∎ )⟩
                 j
              ∎

--------------------------------
--
--
--   Isomorphic arrows from c' to c makes another equalizer
--
--           e eqa f g        f
--         c ----------> a ------->b
--        |^
--        ||
--    h   || h-1
--        v|
--         c'

equalizer+iso : {a b c c' : Obj A } {f g : Hom A a b } {e : Hom A c a } 
                (h-1 : Hom A c' c ) → (h : Hom A c c' ) →
                A [ A [ h o h-1 ]  ≈ id1 A c' ] → A [ A [ h-1  o h ]  ≈ id1 A c ] →
                ( eqa : Equalizer A e f g ) 
           → Equalizer A (A [ e  o h-1  ] ) f g
equalizer+iso  {a} {b} {c} {c'} {f} {g} {e} h-1 h  hh-1=1 h-1h=1  eqa =  record {
      fe=ge = fe=ge1 ;
      k = λ j eq → A [ h o k eqa j eq ] ;
      ek=h = ek=h1 ;
      uniqueness = uniqueness1
  } where
      fe=ge1 :  A [ A [ f o  A [ e  o h-1  ]  ]  ≈ A [ g o  A [ e  o h-1  ]  ] ]
      fe=ge1 = f1=gh ( fe=ge eqa )
      ek=h1 :   {d : Obj A} {j : Hom A d a} {eq : A [ A [ f o j ] ≈ A [ g o j ] ]} →
                A [ A [  A [ e  o h-1  ]  o A [ h o k eqa j eq ] ] ≈ j ]
      ek=h1 {d} {j} {eq} =  let open ≈-Reasoning (A) in
             begin
                   ( e  o h-1 )  o ( h o k eqa j eq )
             ≈↑⟨ assoc ⟩
                    e o ( h-1  o ( h  o k eqa j eq  ) )
             ≈⟨ cdr assoc ⟩
                    e o (( h-1  o  h)  o k eqa j eq  ) 
             ≈⟨ cdr (car h-1h=1 )  ⟩
                    e o (id c  o k eqa j eq  ) 
             ≈⟨ cdr idL  ⟩
                    e o  k eqa j eq  
             ≈⟨ ek=h eqa ⟩
                   j
             ∎
      uniqueness1 : {d : Obj A} {h' : Hom A d a} {eq : A [ A [ f o h' ] ≈ A [ g o h' ] ]} {j : Hom A d c'} →
                A [ A [  A [ e  o h-1 ]  o j ] ≈ h' ] →
                A [ A [ h o k eqa h' eq ] ≈ j ]
      uniqueness1 {d} {h'} {eq} {j} ej=h  =  let open ≈-Reasoning (A) in
             begin
                   h o k eqa h' eq
             ≈⟨ cdr (uniqueness eqa ( begin
                    e o ( h-1 o j  )
                 ≈⟨ assoc ⟩
                   (e o  h-1 ) o j  
                 ≈⟨ ej=h ⟩
                    h'
             ∎ )) ⟩
                   h o  ( h-1 o j )
             ≈⟨ assoc  ⟩
                   (h o   h-1 ) o j 
             ≈⟨ car hh-1=1  ⟩
                   id c' o j 
             ≈⟨ idL ⟩
                   j
             ∎

--------------------------------
--
-- If we have two equalizers on c and c', there are isomorphic pair h, h'
--
--     h : c → c'  h' : c' → c
--     e' = h   o e
--     e  = h'  o e'
--
--
--
--           e eqa f g        f
--         c ---------->a ------->b
--         ^            ^     g
--         |            |
--         |k = id c'   |
--         v            |
--         c'-----------+
--           e eqa' f g

c-iso-l : { c c' a b : Obj A } {f g : Hom A a b } →  {e : Hom A c a } { e' : Hom A c' a }
       ( eqa : Equalizer A e f g) → ( eqa' :  Equalizer A e' f g )
      → Hom A c c'         
c-iso-l  {c} {c'} eqa eqa' = k eqa' (equalizer eqa) ( fe=ge eqa )

c-iso-r : { c c' a b : Obj A } {f g : Hom A a b } →  {e : Hom A c a } { e' : Hom A c' a }
       ( eqa : Equalizer A e f g) → ( eqa' :  Equalizer A e' f g )
      → Hom A c' c         
c-iso-r  {c} {c'} eqa eqa' = k eqa (equalizer eqa') ( fe=ge eqa' )

c-iso-lr : { c c' a b : Obj A } {f g : Hom A a b } →  {e : Hom A c a } { e' : Hom A c' a }
       ( eqa : Equalizer A e f g) → ( eqa' :  Equalizer A e' f g ) →
  A [ A [ c-iso-l eqa eqa' o c-iso-r eqa eqa' ]  ≈ id1 A c' ]
c-iso-lr  {c} {c'} {a} {b} {f} {g} {e} {e'} eqa eqa' =  let open ≈-Reasoning (A) in begin
                  c-iso-l eqa eqa' o c-iso-r eqa eqa'
              ≈⟨⟩
                  k eqa' (equalizer eqa) ( fe=ge eqa )  o  k eqa (equalizer eqa') ( fe=ge eqa' )
              ≈↑⟨ uniqueness eqa' ( begin
                  e' o ( k eqa' (equalizer eqa) (fe=ge eqa) o k eqa (equalizer eqa') (fe=ge eqa') )
              ≈⟨ assoc  ⟩
                  ( e' o  k eqa' (equalizer eqa) (fe=ge eqa) ) o k eqa (equalizer eqa') (fe=ge eqa') 
              ≈⟨ car (ek=h eqa') ⟩
                  e o k eqa (equalizer eqa') (fe=ge eqa') 
              ≈⟨ ek=h eqa ⟩
                  e'
              ∎ )⟩
                 k eqa' e' ( fe=ge eqa' )
              ≈⟨ uniqueness eqa' ( begin
                   e' o id c'
              ≈⟨ idR ⟩
                   e'
              ∎ )⟩
                 id c'
              ∎

-- c-iso-rl is obvious from the symmetry


--------------------------------
----
--
-- Existence of equalizer satisfies Burroni equations
--
----

lemma-equ1 : {a b c : Obj A} (f g : Hom A a b)  → (e : Hom A c a ) →
         ( eqa : {a b c : Obj A} → (f g : Hom A a b)  → {e : Hom A c a }  → Equalizer A e f g ) 
              → Burroni A {c} {a} {b} f g e
lemma-equ1  {a} {b} {c} f g e eqa  = record {
      α = λ {a} {b} {c}  f g e  →  equalizer (eqa {a} {b} {c} f g {e} ) ; -- Hom A c a
      γ = λ {a} {b} {c} {d} f g h → k (eqa f g ) {d} ( A [ h  o (equalizer ( eqa (A [ f  o  h ] ) (A [ g o h ] ))) ] ) 
                            (lemma-equ4 {a} {b} {c} {d} f g h ) ;  -- Hom A c d
      δ =  λ {a} {b} {c} e f → k (eqa {a} {b} {c} f f {e} ) (id1 A a)  (f1=f1 f); -- Hom A a c
      cong-α = λ {a b c e f g g'} eq → cong-α1 {a} {b} {c} {e} {f} {g} {g'} eq ;
      cong-γ = λ {a} {_} {c} {d} {f} {g} {h} {h'} eq → cong-γ1 {a}  {c} {d} {f} {g} {h} {h'} eq  ;
      cong-δ = λ {a b c e f f'} f=f' → cong-δ1 {a} {b} {c} {e} {f} {f'} f=f'  ;
      b1 = fe=ge (eqa {a} {b} {c} f g {e}) ;
      b2 = lemma-b2 ;
      b3 = lemma-b3 ;
      b4 = lemma-b4
 } where
     --
     --           e eqa f g        f
     --         c ----------> a ------->b
     --         ^                  g
     --         |
     --         |k₁  = e eqa (f o (e (eqa f g))) (g o (e (eqa f g))))
     --         |
     --         d
     --
     --
     --               e  o id1 ≈  e  →   k e  ≈ id

     lemma-b3 : {a b d : Obj A} (f : Hom A a b ) { h : Hom A d a } → A [ A [ equalizer (eqa f f ) o k (eqa f f) (id1 A a) (f1=f1 f) ] ≈ id1 A a  ]
     lemma-b3 {a} {b} {d} f {h} = let open ≈-Reasoning (A) in
             begin
                  equalizer (eqa f f) o k (eqa f f) (id a) (f1=f1 f)
             ≈⟨ ek=h (eqa f f )  ⟩
                  id a
             ∎
     lemma-equ4 :  {a b c d : Obj A}  → (f : Hom A a b) → (g : Hom A a b ) → (h : Hom A d a ) →
                      A [ A [ f o A [ h o equalizer (eqa (A [ f o h ]) (A [ g o h ])) ] ] ≈ A [ g o A [ h o equalizer (eqa (A [ f o h ]) (A [ g o h ])) ] ] ]
     lemma-equ4 {a} {b} {c} {d} f g h  = let open ≈-Reasoning (A) in
             begin
                   f o ( h o equalizer (eqa (f o h) ( g o h )))
             ≈⟨ assoc ⟩
                   (f o h) o equalizer (eqa (f o h) ( g o h ))
             ≈⟨ fe=ge (eqa (A [ f o h ]) (A [ g o h ])) ⟩
                   (g o h) o equalizer (eqa (f o h) ( g o h ))
             ≈↑⟨ assoc ⟩
                   g o ( h o equalizer (eqa (f o h) ( g o h )))
             ∎
     cong-α1 : {a b c :  Obj A } → { e : Hom A c a }
          → {f g g' : Hom A a b } →  A [ g ≈ g' ] → A [ equalizer (eqa {a} {b} {c} f g {e} )≈ equalizer (eqa {a} {b} {c} f g' {e} ) ] 
     cong-α1 {a} {b} {c} {e} {f} {g} {g'} eq = let open ≈-Reasoning (A) in refl-hom 
     cong-γ1 :  {a c d : Obj A } → {f g : Hom A a b} {h h' : Hom A d a } →  A [ h ≈ h' ] →  { e : Hom A c a} →
                     A [  k (eqa f g {e} ) {d} ( A [ h  o (equalizer ( eqa (A [ f  o  h  ] ) (A [ g o h  ] ) {id1 A d} )) ] ) (lemma-equ4 {a} {b} {c} {d} f g h ) 
                       ≈  k (eqa f g {e} ) {d} ( A [ h' o (equalizer ( eqa (A [ f  o  h' ] ) (A [ g o h' ] ) {id1 A d} )) ] ) (lemma-equ4 {a} {b} {c} {d} f g h' )  ]
     cong-γ1 {a} {c} {d} {f} {g} {h} {h'} h=h' {e} = let open ≈-Reasoning (A) in begin
                 k (eqa f g ) {d} ( A [ h  o (equalizer ( eqa (A [ f  o  h  ] ) (A [ g o h  ] ))) ] ) (lemma-equ4 {a} {b} {c} {d} f g h )
             ≈⟨ uniqueness (eqa f g) ( begin
                 e o k (eqa f g ) {d} ( A [ h' o (equalizer ( eqa (A [ f  o  h' ] ) (A [ g o h' ] ))) ] ) (lemma-equ4 {a} {b} {c} {d} f g h' )
             ≈⟨ ek=h (eqa f g ) ⟩
                 h' o (equalizer ( eqa (A [ f  o  h' ] ) (A [ g o h' ] )))
             ≈↑⟨ car h=h'  ⟩
                 h o (equalizer ( eqa (A [ f  o  h' ] ) (A [ g o h' ] )))
             ∎ )⟩    
                 k (eqa f g ) {d} ( A [ h' o (equalizer ( eqa (A [ f  o  h' ] ) (A [ g o h' ] ))) ] ) (lemma-equ4 {a} {b} {c} {d} f g h' )
             ∎
     cong-δ1 : {a b c : Obj A} {e : Hom A c a } {f f' : Hom A a b} → A [ f ≈ f' ] →  A [ k (eqa {a} {b} {c} f f {e} ) (id1 A a)  (f1=f1 f)  ≈ 
                                                                            k (eqa {a} {b} {c} f' f' {e} ) (id1 A a)  (f1=f1 f') ]
     cong-δ1 {a} {b} {c} {e} {f} {f'} f=f' =  let open ≈-Reasoning (A) in
             begin
                 k (eqa {a} {b} {c} f  f  {e} ) (id a)  (f1=f1 f) 
             ≈⟨  uniqueness (eqa f f) ( begin
                 e o k (eqa {a} {b} {c} f' f' {e} ) (id a)  (f1=f1 f') 
             ≈⟨ ek=h (eqa {a} {b} {c} f' f' {e} ) ⟩
                 id a
             ∎ )⟩
                 k (eqa {a} {b} {c} f' f' {e} ) (id a)  (f1=f1 f') 
             ∎

     lemma-b2 :  {d : Obj A} {h : Hom A d a} → A [
                      A [ equalizer (eqa f g) o k (eqa f g) (A [ h o equalizer (eqa (A [ f o h ]) (A [ g o h ])) ]) (lemma-equ4 {a} {b} {c} f g h) ]
                    ≈ A [ h o equalizer (eqa (A [ f o h ]) (A [ g o h ])) ] ]
     lemma-b2 {d} {h} = let open ≈-Reasoning (A) in
             begin
                    equalizer (eqa f g) o k (eqa f g) (h o equalizer (eqa (f o h) (g o h))) (lemma-equ4 {a} {b} {c} f g h)
             ≈⟨ ek=h (eqa f g)  ⟩
                    h o equalizer (eqa (f o h ) ( g o h ))
             ∎

     lemma-b4 : {d : Obj A} {j : Hom A d c} → A [
              A [ k (eqa f g) (A [ A [ equalizer (eqa f g) o j ] o 
                              equalizer (eqa (A [ f o A [ equalizer (eqa f g {e}) o j ] ]) (A [ g o A [ equalizer (eqa f g {e} ) o j ] ])) ])
                     (lemma-equ4 {a} {b} {c} f g (A [ equalizer (eqa f g) o j ])) 
                 o k (eqa (A [ f o A [ equalizer (eqa f g) o j ] ]) (A [ f o A [ equalizer (eqa f g) o j ] ])) 
                     (id1 A d) (f1=f1 (A [ f o A [ equalizer (eqa f g) o j ] ])) ]
              ≈ j ]
     lemma-b4 {d} {j} = let open ≈-Reasoning (A) in
             begin
                ( k (eqa f g) (( ( equalizer (eqa f g) o j ) o equalizer (eqa (( f o ( equalizer (eqa f g {e}) o j ) )) (( g o ( equalizer (eqa f g {e}) o j ) ))) ))
                            (lemma-equ4 {a} {b} {c} f g (( equalizer (eqa f g) o j ))) o
                   k (eqa (( f o ( equalizer (eqa f g) o j ) )) (( f o ( equalizer (eqa f g) o j ) ))) (id1 A d) (f1=f1 (( f o ( equalizer (eqa f g) o j ) ))) )
             ≈⟨ car ((uniqueness (eqa f g) ( begin
                         equalizer (eqa f g) o j 
                ≈↑⟨ idR  ⟩
                         (equalizer (eqa f g) o j )  o id d
                ≈⟨⟩         -- here we decide e (fej) (gej)' is id d
                        ((equalizer (eqa f g) o j) o equalizer (eqa (f o equalizer (eqa f g {e}) o j) (g o equalizer (eqa f g {e}) o j)))
             ∎ ))) ⟩
                    j o k (eqa (( f o ( equalizer (eqa f g) o j ) )) (( f o ( equalizer (eqa f g) o j ) ))) (id1 A d) (f1=f1 (( f o ( equalizer (eqa f g) o j ) ))) 
             ≈⟨ cdr ((uniqueness (eqa (( f o ( equalizer (eqa f g) o j ) )) (( f o ( equalizer (eqa f g) o j ) ))) ( begin
                     equalizer (eqa (f o equalizer (eqa f g {e} ) o j) (f o equalizer (eqa f g {e}) o j))  o id d
                ≈⟨ idR ⟩
                     equalizer (eqa (f o equalizer (eqa f g {e}) o j) (f o equalizer (eqa f g {e}) o j))  
                ≈⟨⟩         -- here we decide e (fej) (fej)' is id d
                    id d
             ∎ ))) ⟩
                    j o id d
                ≈⟨ idR ⟩
                    j
             ∎ 

--------------------------------
--
-- Bourroni equations gives an Equalizer
--

lemma-equ2 : {a b c : Obj A} (f g : Hom A a b)  (e : Hom A c a )
         → ( bur : Burroni A {c} {a} {b} f g e ) → Equalizer A {c} {a} {b} (α bur f g e) f g 
lemma-equ2 {a} {b} {c} f g e bur = record {
      fe=ge = fe=ge1 ;  
      k = k1 ;
      ek=h = λ {d} {h} {eq} → ek=h1 {d} {h} {eq} ;
      uniqueness  = λ {d} {h} {eq} {k'} ek=h → uniqueness1  {d} {h} {eq} {k'} ek=h
   } where
      k1 :  {d : Obj A} (h : Hom A d a) → A [ A [ f o h ] ≈ A [ g o h ] ] → Hom A d c
      k1 {d} h fh=gh = β bur {d} {a} {b} f g h
      fe=ge1 : A [ A [ f o (α bur f g e) ] ≈ A [ g o (α bur f g e) ] ]
      fe=ge1 = b1 bur
      ek=h1 : {d : Obj A}  → ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  A [ A [ (α bur f g e)  o k1 {d} h eq ] ≈ h ]
      ek=h1 {d} {h} {eq} =  let open ≈-Reasoning (A) in
             begin
                 α bur f g e o k1 h eq 
             ≈⟨⟩
                 α bur f g e o ( γ bur {a} {b} {c} f g h o δ bur {d} {b} {d} (id d) (f o h) )
             ≈⟨ assoc ⟩
                 ( α bur f g e o  γ bur {a} {b} {c} f g h ) o δ bur {d} {b} {d} (id d) (f o h) 
             ≈⟨ car (b2 bur) ⟩
                  ( h o ( α bur ( f o h ) ( g o h ) (id d))) o δ bur {d} {b} {d} (id d) (f o h) 
             ≈↑⟨ assoc ⟩
                   h o ((( α bur ( f o h ) ( g o h ) (id d) )) o δ bur {d} {b} {d} (id d) (f o h)  )
             ≈↑⟨ cdr ( car ( cong-α bur eq)) ⟩
                   h o ((( α bur ( f o h ) ( f o h ) (id d)))o δ bur {d} {b} {d} (id d) (f o h)  )
             ≈⟨ cdr (b3 bur {d} {b} {d} (f  o h) {id d} ) ⟩
                   h o id d
             ≈⟨ idR ⟩
                 h 
             ∎
      uniqueness1 : {d : Obj A} →  ∀ {h : Hom A d a} →  {eq : A [ A [ f  o  h ] ≈ A [ g  o h ] ] } →  {k' : Hom A d c } →
              A [ A [ (α bur f g e) o k' ] ≈ h ] → A [ k1 {d} h eq  ≈ k' ]
      uniqueness1 {d} {h} {eq} {k'} ek=h =   let open ≈-Reasoning (A) in
             begin
                k1 {d} h eq
             ≈⟨⟩
                γ bur {a} {b} {c} f g h o δ bur {d} {b} {d} (id d) (f o h)
             ≈↑⟨ car (cong-γ bur {a} {b} {c} {d} ek=h ) ⟩
                γ bur f g (A [ α bur f g e o k' ]) o δ bur {d} {b} {d} (id d) (f o h)
             ≈↑⟨ cdr (cong-δ bur (resp ek=h refl-hom )) ⟩
                γ bur f g (A [ α bur f g e o k' ]) o δ bur {d} {b} {d} (id d) ( f o ( α bur f g e o k') ) 
             ≈⟨ b4 bur ⟩
                 k'
             ∎


-- end





