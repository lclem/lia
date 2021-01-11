---
title: "Higher-order recursion 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.HigherOrder where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_; _$_; trans-⊑; refl-⊑) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _∸_ to _-ℕ_; _≤_ to _≤ℕ_) public
```

# Syntax

## Types

```
data Type : Set where
  Int : Type
  _*_ _⟶_ : (τ₀ τ₁ : Type) → Type
```

## Expressions

```
VarName = ℕ

x₀ x₁ f₀ f₁ : VarName
x₀ = 0
x₁ = 1
f₀ = 2
f₁ = 3

data Exp : Set where

  #_ : (n : ℕ) → Exp

  `_ : (x : VarName) → Exp

  _+_ _-_ _*_ : (e₀ e₁ : Exp) → Exp

  If_Then_Else_ : (e₀ e₁ e₂ : Exp) → Exp

  _,_ : (e₀ e₁ : Exp) → Exp
  π₀_ π₁_ : (e : Exp) → Exp

  ƛ_·_ : (x : VarName) (e : Exp) → Exp
  _·_ : (f : VarName) (e : Exp) → Exp

  μ_·_ : (f : VarName) (e : Exp) → Exp

infix 50 #_ `_
infixl 25 _+_ _-_
infixl 26 _*_
infixl 30 _·_
infixr 20 If_Then_Else_
infixr 19 _,_
infixr 18 π₀_ π₁_
infixr 17 ƛ_·_ μ_·_

private
  variable
    x y f : VarName
    e e′ e₀ e₁ e₂ : Exp
    k k′ k₀ k₁ m n n₀ n₁ : ℕ
```

```
```

Example:

```
factorial : Exp
factorial = μ f₀ · ƛ x₀ · If ` x₀ Then # 1 Else ` x₀ * f₀ · ` x₀ - # 1
```

# Eager evaluation with dynamic binding

```
```

# Eager evaluation with static binding

# Lazy evaluation with dynamic binding

# Lazy evaluation with static binding
