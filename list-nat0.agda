module list-nat0 where
                                                                        
open import Level


postulate a : Set
postulate b : Set
postulate c : Set


infixr 40 _::_
data  List ∀ {a} (A : Set a) : Set a where
   [] : List A
   _::_ : A -> List A -> List A


infixl 30 _++_
-- _++_ : {a : Level } -> {A : Set a} -> List A -> List A -> List A
_++_ : ∀ {a} {A : Set a} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)


l1 = a :: []
l2 = a :: b :: a :: c ::  []

l3 = l1 ++ l2

infixr 20  _==_

data _==_ {n} {A : Set n} :  List A -> List A -> Set n where
      reflection  : {x : List A} -> x == x
      eq-cons : {x y : List A} { a : A } -> x ==  y -> ( a :: x ) == ( a :: y )
      trans-list : {x y z : List A} { a : A } -> x ==  y -> y == z -> x == z
--      eq-nil  : [] == []

list-id-l : { A : Set } -> { x : List A} ->  [] ++ x == x
list-id-l = reflection

list-id-r : { A : Set } -> ( x : List A ) ->  x ++ [] == x
list-id-r [] =   reflection
list-id-r (x :: xs) =  eq-cons ( list-id-r xs )


-- listAssoc : { A : Set } -> { a b c : List A} ->  ( ( a ++ b ) ++ c ) == ( a ++ ( b ++ c ) )
-- listAssoc   = eq-reflection

list-assoc : {A : Set } -> ( xs ys zs : List A ) ->
     ( ( xs ++ ys ) ++ zs ) == ( xs ++ ( ys ++ zs ) )
list-assoc  [] ys zs = reflection
list-assoc  (x :: xs)  ys zs = eq-cons ( list-assoc xs ys zs )



open  import  Relation.Binary.PropositionalEquality
open ≡-Reasoning

cong1 : ∀{a} {A : Set a } {b} { B : Set b } ->
   ( f : A -> B ) -> {x : A } -> {y : A} -> x ≡ y -> f x ≡ f y
cong1 f refl = refl

lemma11 :  ∀{n} ->  ( Set n ) IsRelatedTo ( Set n )
lemma11  = relTo refl

lemma12 : {L : Set}  ( x : List L ) -> x ++ x ≡ x ++ x
lemma12 x =  begin  x ++ x  ∎


++-assoc : {L : Set} ( xs ys zs : List L ) -> (xs ++ ys) ++ zs  ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = -- {A : Set} ->  -- let open ==-Reasoning A in
  begin -- to prove ([] ++ ys) ++ zs  ≡ [] ++ (ys ++ zs)
   ( [] ++ ys ) ++ zs
  ≡⟨ refl ⟩
    ys ++ zs
  ≡⟨ refl ⟩
    [] ++ ( ys ++ zs )
  ∎
  
++-assoc (x :: xs) ys zs = -- {A : Set} -> -- let open  ==-Reasoning A in
  begin -- to prove ((x :: xs) ++ ys) ++ zs ≡ (x :: xs) ++ (ys ++ zs)
    ((x :: xs) ++ ys) ++ zs
  ≡⟨ refl ⟩
     (x :: (xs ++ ys)) ++ zs
  ≡⟨ refl ⟩
    x :: ((xs ++ ys) ++ zs)
  ≡⟨ cong1 (_::_ x) (++-assoc xs ys zs) ⟩ 
    x :: (xs ++ (ys ++ zs))
  ≡⟨ refl ⟩
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

