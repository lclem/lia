---
title: "The untyped lambda calculus 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Untyped where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_; _$_; trans-⊑; refl-⊑) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _∸_ to _-ℕ_; _≤_ to _≤ℕ_) public
open import part5.Maybe
```

# Syntax

```
VarName = ℕ

data Exp : Set where

  `_ : (x : VarName) → Exp

  ƛ_⇒_ : (x : VarName) (e : Exp) → Exp
  _·_ : (e₀ e₁ : Exp) → Exp

infix 50 `_
infixl 30 _·_
infixr 17 ƛ_⇒_

private
  variable
    x : VarName
    e e′ e₀ e₁ e₂ : Exp
```

Example:

```
-- factorial : Exp
-- factorial = μ f₀ · ƛ x₀ · (If (` x₀) Then (# 1) Else ((` x₀) * ((` f₀) · (` x₀ - (# 1)))))
```

Free variables:

```
∅ : VarName *
∅ = ε

fv : Exp → VarName *
fv (` x) = [ x ]
fv (ƛ x ⇒ e) = remove x (fv e)
fv (e₀ · e₁) = fv e₀ ++ fv e₁
```

Closed expressions:

```
Closed : Exp → Set
Closed e = fv e ≡ ∅
```

# Eager evaluation with dynamic binding

## Big-steps operational semantics

```
Env = VarName → Exp

private
  variable
    ϱ : Env
    u u₀ u₁ v v₀ v₁ : Exp

infix 10 _⊢_⇒_
data _⊢_⇒_ : Env → Exp → Exp → Set where

  Var : ϱ ⊢ ` x ⇒ ϱ x

  Abs : ---------------------
        ϱ ⊢ ƛ x ⇒ e ⇒ ƛ x ⇒ e

  App : ϱ ⊢ e₀ ⇒ ƛ x ⇒ e →
        ϱ ⊢ e₁ ⇒ v₁ →
        ϱ [ x ↦ v₁ ] ⊢ e ⇒ v →
        ----------------------
        ϱ ⊢ e₀ · e₁ ⇒ v
```

TODO: Illustrate the dynamic binding aspect.

### Deterministic values

```
det : ϱ ⊢ e ⇒ u →
      ϱ ⊢ e ⇒ v →
      -----------
      u ≡ v

det δ σ = {!   !}
```

## Denotational semantics

Evaluation with gas.

-- You actually need a Krivine machine!

```
Exp⊥ = Maybe Exp

⟦_⟧_#_ : Exp → Env → ℕ → Exp⊥

⟦ e ⟧ ϱ # 0 = ⊥

⟦ ` x ⟧ ϱ # suc n = ⌊ ϱ x ⌋

⟦ ƛ x ⇒ e ⟧ ϱ # suc n = ⌊ ƛ x ⇒ e ⌋

⟦ e₀ · e₁ ⟧ ϱ # suc n
  with ⟦ e₀ ⟧ ϱ # n | ⟦ e₁ ⟧ ϱ # n
... | ⌊ ƛ x ⇒ e ⌋ | ⌊ v ⌋ = ⟦ e ⟧ ϱ [ x ↦ v ] # n
... | _ | _ = ⊥ -- this is catching many cases
```

Example:

```
ϱ₀ : Env
ϱ₀ _ = ` 0

f y : VarName
f = 2
y = 3

0ᶜ 1ᶜ 2ᶜ : Exp
0ᶜ = ƛ f ⇒ ƛ y ⇒ ` y
1ᶜ = ƛ f ⇒ ƛ y ⇒ ` f · ` y
2ᶜ = ƛ f ⇒ ƛ y ⇒ ` f · ` f · ` y

_ᶜ : ℕ → Exp
zero ᶜ = 0ᶜ
suc n ᶜ = {!   !}
```

## Agreement of the operational and denotational semantics

# Eager evaluation with static binding

# Lazy evaluation with dynamic binding

# Lazy evaluation with static binding
