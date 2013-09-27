module category-ex where

open import Level
open import Category
postulate c₁ c₂ ℓ : Level
postulate A : Category c₁ c₂ ℓ

postulate a b c : Obj A
postulate g : Hom A a b
postulate f : Hom A b c

open Category.Category

h = _o_  A f g

i = A [ f o g ]


