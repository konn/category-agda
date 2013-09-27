module idF where

open import Category
open import HomReasoning

identityFunctor : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → Functor C C
identityFunctor {C = C} = record { 
       FObj      = λ x → x
     ; FMap      = λ x → x
     ; isFunctor = isFunctor
     }
  where
        isFunctor : ∀{c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} → IsFunctor C C (λ x → x) (λ x → x)
        isFunctor {C = C} =
          record { ≈-cong   = Lemma1
                 ; identity = Lemma2
                 ; distr    = Lemma3
                 } where
           FMap : {a b : Obj C} -> Hom C a b -> Hom C a b
           FMap = λ x → x
           FObj : Obj C -> Obj C
           FObj = λ x → x
           Lemma1 : {A B : Obj C} {f g : Hom C A B} → C [ f ≈ g ] → C [ FMap f ≈ FMap g ]
           Lemma1 {a} {b} {f} {g}  f≈g = let open ≈-Reasoning C in
             begin
                 FMap f 
             ≈⟨⟩ 
                 f
             ≈⟨ f≈g  ⟩ 
                 g
             ≈⟨⟩ 
                 FMap g 
             ∎ 
           Lemma2 : {A : Obj C} →  C [ (FMap {A} {A} (Id {_} {_} {_} {C} A)) ≈ (Id {_} {_} {_} {C} (FObj A)) ]
           Lemma2 {A} = let open ≈-Reasoning C in
             begin
                   (FMap {A} {A} (Id {_} {_} {_} {C} A))
             ≈⟨⟩ 
                   (Id {_} {_} {_} {C} (FObj A))
             ∎ 
           Lemma3 : {a b c : Obj C} {f : Hom C a b} {g : Hom C b c}
              → C [ FMap (C [ g o f ]) ≈ (C [ FMap g o FMap f ] )]
           Lemma3 {a} {b} {c} {f} {g}  = let open ≈-Reasoning C in
             begin
                FMap ( g o f ) 
             ≈⟨⟩ 
                g o f 
             ≈⟨⟩ 
                FMap g o FMap f 
             ∎ 





