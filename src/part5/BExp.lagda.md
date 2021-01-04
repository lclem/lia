---
title: "Boolean expressions 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.BExp where
open import part5.AExp public
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
  and : BExp → BExp → BExp
  or : BExp → BExp → BExp
  not : BExp → BExp
  leq : AExp → AExp → BExp
```

## **Exercise**: `⟦_⟧B_`

Define the denotational semantics of boolean expressions.

*Hint:* In the `leq` case you will need `_≤?_`.

```
infix 10 ⟦_⟧B_
⟦_⟧B_ : BExp → Env → 𝔹
⟦ b ⟧B ρ = {!   !}
```