open import Category -- https://github.com/konn/category-agda                                                                                     
open import Algebra
open import Level
open import Category.Sets
module monoid-monad {c : Level} where

open import Algebra.Structures
open import HomReasoning
open import cat-utility
open import Category.Cat
open import Data.Product
open import Relation.Binary.Core
open import Relation.Binary

-- open Monoid
open import Algebra.FunctionProperties using (Op₁; Op₂)


record ≡-Monoid c : Set (suc c) where
  infixl 7 _∙_
  field
    Carrier  : Set c
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≡_ _∙_ ε

postulate M : ≡-Monoid c
open ≡-Monoid

A = Sets {c}

-- T : A → (M x A)

T : Functor A A
T = record {
        FObj = λ a → (Carrier M) × a
        ; FMap = λ f → map ( λ x → x ) f
        ; isFunctor = record {
             identity = IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory Sets ))
             ; distr = (IsEquivalence.refl (IsCategory.isEquivalence  ( Category.isCategory Sets )))
             ; ≈-cong = cong1
        } 
    } where
        cong1 : {ℓ′ : Level} → {a b : Set ℓ′} { f g : Hom (Sets {ℓ′}) a b} → 
                   Sets [ f ≈ g ] → Sets [ map (λ (x : Carrier M) → x) f ≈ map (λ (x : Carrier M) → x) g ]
        cong1 _≡_.refl = _≡_.refl

open Functor

Lemma-MM1 :  {a b : Obj A} {f : Hom A a b} →
        A [ A [ FMap T f o (λ x → ε M , x) ] ≈
        A [ (λ x → ε M , x) o f ] ]
Lemma-MM1 {a} {b} {f} = let open ≈-Reasoning A renaming ( _o_ to _*_ ) in 
        begin
             FMap T f o (λ x → ε M , x)
        ≈⟨⟩
             (λ x → ε M , x) o f
        ∎

-- η : a → (ε,a)
η : NTrans  A A identityFunctor T
η = record {
       TMap = λ a → λ(x : a) → ( ε M , x ) ;
       isNTrans = record {
            commute = Lemma-MM1
       }
  }

-- μ : (m,(m',a)) → (m*m,a)

muMap : (a : Obj A  ) → FObj T ( FObj T a ) → Σ (Carrier M) (λ x → a )
muMap a ( m , ( m' , x ) ) = ( _∙_ M m  m'  ,  x )

Lemma-MM2 :  {a b : Obj A} {f : Hom A a b} →
        A [ A [ FMap T f o (λ x → muMap a x) ] ≈
        A [ (λ x → muMap b x) o FMap (T ○ T) f ] ]
Lemma-MM2 {a} {b} {f} =  let open ≈-Reasoning A renaming ( _o_ to _*_ ) in                                                       
        begin
             FMap T f o (λ x → muMap a x)
        ≈⟨⟩
             (λ x → muMap b x) o FMap (T ○ T) f
        ∎

μ : NTrans  A A ( T ○ T ) T
μ = record {
       TMap = λ a → λ x  → muMap a x ; 
       isNTrans = record {
            commute = λ{a} {b} {f} → Lemma-MM2 {a} {b} {f}
       }
  }

open NTrans

Lemma-MM33 : {a : Level} {b : Level} {A : Set a} {B : A → Set b}  {x :  Σ A B } →  (((proj₁ x) , proj₂ x ) ≡ x )
Lemma-MM33 =  _≡_.refl

Lemma-MM34 : ∀( x : Carrier M  ) → ( (M ∙ ε M) x ≡ x  )
Lemma-MM34  x = (( proj₁ ( IsMonoid.identity ( isMonoid M )) ) x )

Lemma-MM35 : ∀( x : Carrier M  ) → ((M ∙ x) (ε M))  ≡ x
Lemma-MM35  x = ( proj₂  ( IsMonoid.identity ( isMonoid M )) ) x

Lemma-MM36 : ∀( x y z : Carrier M ) → ((M ∙ (M ∙ x) y) z)  ≡ (_∙_ M  x (_∙_ M y z ) )
Lemma-MM36  x y z = ( IsMonoid.assoc ( isMonoid M ))  x y z

-- Functional Extensionality Axiom (We cannot prove this in Agda / Coq, just assumming )
import Relation.Binary.PropositionalEquality
-- postulate extensionality : { a b : Obj A } {f g : Hom A a b } →  Relation.Binary.PropositionalEquality.Extensionality c c
postulate extensionality : Relation.Binary.PropositionalEquality.Extensionality c c

-- Multi Arguments Functional Extensionality
extensionality30 : {f g : Carrier M → Carrier M → Carrier M → Carrier M } → 
               (∀ x y z  → f x y z ≡ g x y z )  → ( f ≡ g ) 
extensionality30 eq = extensionality ( \x -> extensionality ( \y -> extensionality (eq x y) ) )

Lemma-MM9  : ( λ(x : Carrier M) → ( M ∙ ε M ) x )  ≡ ( λ(x : Carrier M) → x ) 
Lemma-MM9  = extensionality Lemma-MM34

Lemma-MM10 : ( λ x →   ((M ∙ x) (ε M)))  ≡ ( λ x → x ) 
Lemma-MM10  = extensionality Lemma-MM35

Lemma-MM11 : (λ x y z → ((M ∙ (M ∙ x) y) z))  ≡ (λ x y z → ( _∙_ M  x (_∙_ M y z ) ))
Lemma-MM11 = extensionality30 Lemma-MM36 

MonoidMonad : Monad A T η μ 
MonoidMonad = record {
       isMonad = record {
           unity1 = Lemma-MM3 ;
           unity2 = Lemma-MM4 ;
           assoc  = Lemma-MM5 
       }  
   } where
       Lemma-MM3 : {a : Obj A} → A [ A [ TMap μ a o TMap η ( FObj T a ) ] ≈ Id {_} {_} {_} {A} (FObj T a) ]
       Lemma-MM3 {a} = let open ≈-Reasoning (A) renaming ( _o_ to _*_ ) in
                begin
                     TMap μ a o TMap η ( FObj T a )
                ≈⟨⟩
                    ( λ x → ((M ∙ ε M) (proj₁ x) , proj₂ x ))
                ≈⟨  cong ( λ f → ( λ x →  ( ( f (proj₁ x) ) , proj₂ x ))) ( Lemma-MM9 )  ⟩
                    ( λ (x : FObj T a) → (proj₁ x) , proj₂ x )
                ≈⟨⟩
                    ( λ x → x )
                ≈⟨⟩
                     Id {_} {_} {_} {A} (FObj T a)
                ∎
       Lemma-MM4 : {a : Obj A} → A [ A [ TMap μ a o (FMap T (TMap η a ))] ≈ Id {_} {_} {_} {A} (FObj T a) ]
       Lemma-MM4 {a} = let open ≈-Reasoning (A) renaming ( _o_ to _*_ ) in
                begin
                     TMap μ a o (FMap T (TMap η a ))
                ≈⟨⟩
                    ( λ x → (M ∙ proj₁ x) (ε M) , proj₂ x )
                ≈⟨  cong ( λ f → ( λ x →  ( f (proj₁ x) ) , proj₂ x )) ( Lemma-MM10 )  ⟩
                    ( λ x → (proj₁ x) , proj₂ x )
                ≈⟨⟩
                    ( λ x → x )
                ≈⟨⟩
                     Id {_} {_} {_} {A} (FObj T a)
                ∎
       Lemma-MM5 : {a : Obj A} → A [ A [ TMap μ a o TMap μ ( FObj T a ) ] ≈  A [  TMap μ a o FMap T (TMap μ a) ] ]
       Lemma-MM5 {a} = let open ≈-Reasoning (A) renaming ( _o_ to _*_ ) in
                begin
                      TMap μ a o TMap μ ( FObj T a ) 
                ≈⟨⟩
                      ( λ x → (M ∙ (M ∙ proj₁ x) (proj₁ (proj₂ x))) (proj₁ (proj₂ (proj₂ x))) , proj₂ (proj₂ (proj₂ x)))
                ≈⟨ cong ( λ f → ( λ x → 
                         (( f ( proj₁ x ) ((proj₁ (proj₂ x))) ((proj₁ (proj₂ (proj₂ x)))  )) ,  proj₂ (proj₂ (proj₂ x)) )
                         )) Lemma-MM11  ⟩
                      ( λ x → (M ∙ proj₁ x) ((M ∙ proj₁ (proj₂ x)) (proj₁ (proj₂ (proj₂ x)))) , proj₂ (proj₂ (proj₂ x)))
                ≈⟨⟩
                      TMap μ a o FMap T (TMap μ a)
                ∎


F  : (m : Carrier M) -> { a b : Obj A } -> ( f : a -> b ) -> Hom A a ( FObj T b )
F m {a} {b} f =  \(x : a ) -> ( m , ( f x) )

postulate m m' : Carrier M
postulate a b c' : Obj A 
postulate f :  b -> c'
postulate g :  a -> b

Lemma-MM12 =  Monad.join MonoidMonad (F m f) (F m' g)

open import kleisli {_} {_} {_} {A} {T} {η} {μ} {MonoidMonad}

-- nat-ε   TMap = λ a₁ → record { KMap = λ x → x }
-- nat-η   TMap = λ a₁ → _,_ (ε,  M)
-- U_T     Functor Kleisli A
-- U_T     FObj = λ B → Σ (Carrier M) (λ x → B)     FMap = λ {a₁} {b₁} f₁ x → ( proj₁ x ∙ (proj₁ (KMap f₁ (proj₂ x)))  , proj₂ (KMap f₁ (proj₂ x))
-- F_T     Functor A Kleisli 
-- F_T     FObj = λ a₁ → a₁                         FMap = λ {a₁} {b₁} f₁ → record { KMap = λ x → ε M , f₁ x }
