module test where

open import part0.Naturals

variable
    ℓ m : Level
    A : Set ℓ
    B : Set m

proj1 : A → B → A
proj1 x y = x

proj2 : A → B → B
proj2 x y = y

data Two : Set where
    one : Two
    two : Two

select : Two → A → A → A
select x a₀ a₁ = {! x !}
















