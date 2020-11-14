---
title: Simplification of formulas 🚧
---

In this chapter we study a procedure to simplify formulas of classical propositional logic.

```
{-# OPTIONS --allow-unsolved-metas  #-}
open import part0.Naturals using (ℕ)

module part1.Simplification (n′ : ℕ) where
open import part0.index
open import part1.Semantics n′
```

# Formula size

When defining functions on formulas,
a straightforward structural induction often suffices.
<!-- as in `props` [above](#occurring-propositions) -->
However, this is not always the case, and for more complicated recursive definitions
we need to use other forms of recursion,
such as [well-founded recursion](../../part0/wf). TODO: FIX THIS LINK.
In such situations, it is useful to have a notion of *size* of a formula in order to show that the size decreases at each step.
The definition of formula size is given by structural induction on `Formula`:

```
size : Formula → ℕ
size ⊤ = 1
size ⊥ = 1
size (` _) = 1
size (¬ φ) = 1 + size φ
size (φ ∧ ψ) = 1 + size φ + size ψ
size (φ ∨ ψ) = 1 + size φ + size ψ
size (φ ⇒ ψ) = 1 + size φ + size ψ
size (φ ⇔ ψ) = 1 + size φ + size ψ
```

!example(#example:size)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
In the example formula `φ₀`, we have:

```
_ : size φ₀ ≡ 6
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:size-neg)(`size-¬`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Prove that !ref(size) satisfies the following two inequalities:

```
size-¬ : ∀ φ → size φ ≤ size (¬ φ)
size-¬¬ : ∀ φ → size φ ≤ size (¬ ¬ φ)
```

(This will be used in the chapter on [Normal Forms](../../part1/NormalForms).)

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
size-¬ _ = n≤sucn
size-¬¬ φ = trans-≤ (size-¬ φ) (size-¬ (¬ φ)) 
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


# Formula simplification


```
simplify : Formula → Formula
simplify (⊥ ∧ φ) = ⊥
simplify (φ ∧ ⊥) = ⊥
simplify (⊤ ∧ φ) = simplify φ
simplify (φ ∧ ⊤) = simplify φ
simplify (⊥ ∨ φ) = simplify φ
simplify (φ ∨ ⊥) = simplify φ
simplify (⊤ ∨ φ) = ⊤
simplify (φ ∨ ⊤) = ⊤
simplify (¬ φ) = ¬ simplify φ
simplify (φ ∧ ψ) = simplify φ ∧ simplify ψ
simplify (φ ∨ ψ) = simplify φ ∨ simplify ψ
simplify φ = φ
```

# Solutions

!solutions
