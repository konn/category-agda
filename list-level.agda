module list-level where
                                                                        
open import Level


postulate A : Set
postulate B : Set
postulate C : Set

postulate a : A
postulate b : A
postulate c : A


infixr 40 _::_
data  List {a} (A : Set a) : Set a where
   [] : List A
   _::_ : A -> List A -> List A


infixl 30 _++_
_++_ : ∀ {a} {A : Set a} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

l1 = a :: []
l2 = a :: b :: a :: c ::  []

l3 = l1 ++ l2

L1 = A :: []
L2 = A :: B :: A :: C ::  []

L3 = L1 ++ L2

data Node {a} ( A : Set a ) : Set a where
   leaf  : A -> Node A
   node  : Node A -> Node A -> Node A

flatten : ∀{n} { A : Set n } -> Node A -> List A
flatten ( leaf a )   = a :: []
flatten ( node a b ) = flatten a ++ flatten b

n1 = node ( leaf a ) ( node ( leaf b ) ( leaf c ))

open  import  Relation.Binary.PropositionalEquality

infixr 20  _==_

data _==_ {n} {A : Set n} :  List A -> List A -> Set n where
      reflection  : {x : List A} -> x == x

cong1 : ∀{a} {A : Set a } {b} { B : Set b } ->
   ( f : List A -> List B ) -> {x : List A } -> {y : List A} -> x == y -> f x == f y
cong1 f reflection = reflection

eq-cons :  ∀{n} {A : Set n} {x y : List A} ( a : A ) -> x ==  y -> ( a :: x ) == ( a :: y )
eq-cons a z = cong1 ( \x -> ( a :: x) ) z

trans-list :  ∀{n} {A : Set n} {x y z : List A}  -> x ==  y -> y == z -> x == z
trans-list reflection reflection = reflection


==-to-≡ :  ∀{n} {A : Set n}  {x y : List A}  -> x ==  y -> x ≡ y
==-to-≡ reflection = refl

list-id-l : { A : Set } -> { x : List A} ->  [] ++ x == x
list-id-l = reflection

list-id-r : { A : Set } -> ( x : List A ) ->  x ++ [] == x
list-id-r [] =   reflection
list-id-r (x :: xs) =  eq-cons x ( list-id-r xs )

list-assoc : {A : Set } -> ( xs ys zs : List A ) ->
     ( ( xs ++ ys ) ++ zs ) == ( xs ++ ( ys ++ zs ) )
list-assoc  [] ys zs = reflection
list-assoc  (x :: xs)  ys zs = eq-cons x ( list-assoc xs ys zs )


module ==-Reasoning {n} (A : Set n ) where

  infixr  2 _∎
  infixr 2 _==⟨_⟩_ _==⟨⟩_
  infix  1 begin_


  data _IsRelatedTo_ (x y : List A) :
                     Set n where
    relTo : (x≈y : x  == y  ) → x IsRelatedTo y

  begin_ : {x : List A } {y : List A} →
           x IsRelatedTo y →  x ==  y 
  begin relTo x≈y = x≈y

  _==⟨_⟩_ : (x : List A ) {y z : List A} →
            x == y  → y IsRelatedTo z → x IsRelatedTo z
  _ ==⟨ x≈y ⟩ relTo y≈z = relTo (trans-list x≈y y≈z)

  _==⟨⟩_ : (x : List A ) {y : List A} 
            → x IsRelatedTo y → x IsRelatedTo y
  _ ==⟨⟩ x≈y = x≈y

  _∎ : (x : List A ) → x IsRelatedTo x
  _∎ _ = relTo reflection

lemma11 : ∀{n} (A : Set n) ( x : List A ) -> x == x
lemma11 A x =  let open ==-Reasoning A in
     begin x ∎
      
++-assoc : ∀{n} (L : Set n) ( xs ys zs : List L ) -> (xs ++ ys) ++ zs  == xs ++ (ys ++ zs)
++-assoc A [] ys zs = let open ==-Reasoning A in
  begin -- to prove ([] ++ ys) ++ zs  == [] ++ (ys ++ zs)
   ( [] ++ ys ) ++ zs
  ==⟨ reflection ⟩
    ys ++ zs
  ==⟨ reflection ⟩
    [] ++ ( ys ++ zs )
  ∎
  
++-assoc A (x :: xs) ys zs = let open  ==-Reasoning A in
  begin -- to prove ((x :: xs) ++ ys) ++ zs == (x :: xs) ++ (ys ++ zs)
    ((x :: xs) ++ ys) ++ zs
  ==⟨ reflection ⟩
     (x :: (xs ++ ys)) ++ zs
  ==⟨ reflection ⟩
    x :: ((xs ++ ys) ++ zs)
  ==⟨ cong1 (_::_ x) (++-assoc A xs ys zs) ⟩ 
    x :: (xs ++ (ys ++ zs))
  ==⟨ reflection ⟩
    (x :: xs) ++ (ys ++ zs)
  ∎



--data Bool : Set where
--      true  : Bool
--      false : Bool


--postulate Obj : Set

--postulate Hom : Obj -> Obj -> Set


--postulate  id : { a : Obj } -> Hom a a


--infixr 80 _○_
--postulate  _○_ : { a b c  : Obj } -> Hom b c -> Hom a b -> Hom a c

-- postulate  axId1 : {a  b : Obj} -> ( f : Hom a b ) -> f == id ○ f
-- postulate  axId2 : {a  b : Obj} -> ( f : Hom a b ) -> f == f ○ id

--assoc : { a b c d : Obj } ->
--    (f : Hom c d ) -> (g : Hom b c) -> (h : Hom a b) ->
--    (f ○ g) ○ h == f ○ ( g ○ h)


--a = Set

-- ListObj : {A : Set} -> List A
-- ListObj =  List Set

-- ListHom : ListObj -> ListObj -> Set

