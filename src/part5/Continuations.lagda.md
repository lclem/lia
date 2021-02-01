---
title: "Continuations 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Continuations where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _≤_ to _≤ℕ_) public
```

```
factorial : ℕ → ℕ
factorial 0 = 0
factorial (suc n) = suc n ·ℕ factorial n

factorial-cont : ℕ → (ℕ → ℕ) → ℕ
factorial-cont 0 κ = κ 0
factorial-cont (suc n) κ = factorial-cont n (λ m → κ (suc n ·ℕ m))

factorial-lemma : ∀ n → factorial n ≡ factorial-cont n id
factorial-lemma n = go n id where

  go : ∀ n κ → κ (factorial n) ≡ factorial-cont n κ
  go zero κ = refl
  go (suc n) κ rewrite go n (λ m → κ (m +ℕ n ·ℕ m)) = refl
```

Exercise: Do the same for Fibonacci.

```
fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib (suc n) +ℕ fib n

fib-cont : ℕ → (ℕ → ℕ) → ℕ
fib-cont 0 κ = κ 0
fib-cont 1 κ = κ 1 
fib-cont (suc (suc n)) κ = fib-cont (suc n) λ a → fib-cont n λ b → κ (a +ℕ b)

fib-lemma : ∀ n → fib-cont n id ≡ fib n
fib-lemma n = go n id where

  go : ∀ n κ → fib-cont n κ ≡ κ (fib n)
  go zero κ = refl
  go (suc zero) κ = refl
  go (suc (suc n)) κ
    rewrite go (suc n) (λ a → fib-cont n (λ b → κ (a +ℕ b))) |
            go n (λ b → κ (fib (suc n) +ℕ b)) = refl
```

Alternative order of evaluation:

```
fib-cont2 : ℕ → (ℕ → ℕ) → ℕ
fib-cont2 0 κ = κ 0
fib-cont2 1 κ = κ 1 
fib-cont2 (suc (suc n)) κ = fib-cont2 n λ a → fib-cont2 (suc n) λ b → κ (a +ℕ b)
```