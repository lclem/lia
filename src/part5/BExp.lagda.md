---
title: "Boolean expressions 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.BExp where
open import part5.AExp hiding (_≤_)
```

We define a simple language of boolan expressions.

## Syntax of expressions

An element in `BExp` is a boolean combination
of atomic expressions of the form `leq e f`,
where `e` and `f` are arithmetic expressions.

```
data BExp : Set where
  tt : BExp
  ff : BExp
  Not : BExp → BExp
  Or : BExp → BExp → BExp
  And : BExp → BExp → BExp
  Leq : AExp → AExp → BExp

pattern _∨_ b₀ b₁ = Or b₀ b₁
pattern _∧_ b₀ b₁ = And b₀ b₁
pattern ¬_ b = Not b
pattern _≤_ e f = Leq e f
```

## **Exercise**: `B⟦_⟧_`

Define the denotational semantics of boolean expressions.

*Hint:* In the `Leq` case you will need `_≤?_`.

```
infix 101 B⟦_⟧_
B⟦_⟧_ : BExp → Env → 𝔹
B⟦ tt ⟧ ρ = tt
B⟦ ff ⟧ ρ = ff
B⟦ ¬ b ⟧ ρ = ¬𝔹 B⟦ b ⟧ ρ
B⟦ b ∨ c ⟧ ρ = B⟦ b ⟧ ρ ∨𝔹 B⟦ c ⟧ ρ
B⟦ b ∧ c ⟧ ρ = B⟦ b ⟧ ρ ∧𝔹 B⟦ c ⟧ ρ
B⟦ e ≤ f ⟧ ρ
  with A⟦ e ⟧ ρ ≤? A⟦ f ⟧ ρ
... | yes _ = tt
... | no _ = ff
```