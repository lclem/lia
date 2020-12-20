---
title: "Gentzen's sequent calculus 🚧"
---

```
{-# OPTIONS --allow-unsolved-meta  #-}

-- --show-implicit --overlapping-instances

open import part0.index

module part1.SequentCalculus (n′ : ℕ) where
open import part1.NaturalDeduction n′ public hiding (_⊢ND_) renaming (_⊢_ to _⊢ND_)
open import part1.NormalForms n′ public

private
  variable
    p q r : PropName
    φ ψ θ ξ : Formula
    Γ Γ₀ Γ₁ Δ Δ₀ Δ₁ Ξ Ψ : Context
```

# Sequent calculus

Sequent calculus is the assembly language of proofs.

## Rules

```
infixr 5 _⊢_
data _⊢_ : Context → Context → Set where
```

We can divide its rules into four groups.

### Axioms

In the first group we have the *axioms*, i.e., rules that do not depend on any previously constructed proof:

```
    instance Ax : [ φ ] ⊢ [ φ ]
    instance ⊥-left : [ ⊥ ] ⊢ ∅
    instance ⊤-right : ∅ ⊢ [ ⊤ ]
```

### Structural rules

In the second group we have the *structural rules*,
which allow us to perform some plumbing within sequents.
The *weakening rules* allow us to introduce new formula into a sequent:

```
    weakening-left : Γ ⊢ Δ →
                     ---------
                     Γ · φ ⊢ Δ

    weakening-right : Γ ⊢ Δ →
                      ---------
                      Γ ⊢ Δ · φ
```

The *exchange rules* allow us to permute formulas within a sequent:

```
    exchange-left : ∀ Γ →
                    Γ ++ [ φ ψ ] ++ Δ ⊢ Ξ →
                    -----------------------
                    Γ ++ [ ψ φ ] ++ Δ ⊢ Ξ

    exchange-right : ∀ Γ →
                     Γ ⊢ Δ ++ [ φ ψ ] ++ Ξ →
                     -----------------------
                     Γ ⊢ Δ ++ [ ψ φ ] ++ Ξ
```

Thus the exchange rules allow us to see a sequent as a multiset of formulas.
Finally, the *contraction rules* allow us to remove duplicated occurrences of the same formula within a sequent:

```
    contraction-left : Γ · φ · φ ⊢ Δ →
                       ---------------
                       Γ · φ ⊢ Δ

    contraction-right : Γ ⊢ Δ · φ · φ →
                        ----------------
                        Γ ⊢ Δ · φ 
```

Taken together, the exchange and contraction rules allow us to see a sequent as a set of formulas.

### Logical rules

In the third group we have the logical rules which allow us to introduce the logical connectives,
both on the left and on the right of the sequent:

```
    ¬-left : Γ ⊢ Δ · φ →
             -----------
             Γ · ¬ φ ⊢ Δ

    ¬-right : Γ · φ ⊢ Δ →
              ------------
              Γ ⊢ Δ · ¬ φ

    ∧-left : Γ · φ · ψ ⊢ Δ →
             -------------
             Γ · φ ∧ ψ ⊢ Δ

    ∧-right : Γ ⊢ Δ · φ →
              Γ ⊢ Δ · ψ →
              -------------
              Γ ⊢ Δ · φ ∧ ψ

    ∨-left : Γ · φ ⊢ Δ →
             Γ · ψ ⊢ Δ →
             ------------
             Γ · φ ∨ ψ ⊢ Δ

    ∨-right : Γ ⊢ Δ · φ · ψ →
              ---------------
              Γ ⊢ Δ · φ ∨ ψ

    ⇒-left : Γ ⊢ Δ · φ →
             Γ · ψ ⊢ Ξ →
             ------------------
             Γ · φ ⇒ ψ ⊢ Δ ++ Ξ

    ⇒-right : Γ · φ ⊢ Δ · ψ →
              -------------
              Γ ⊢ Δ · φ ⇒ ψ

    ⇔-left : Γ ⊢ Δ · φ · ψ →
             Γ · φ · ψ ⊢ Ξ →
             ------------------
             Γ · φ ⇔ ψ ⊢ Δ ++ Ξ

    ⇔-right : Γ · φ ⊢ Δ · ψ →
              Γ · ψ ⊢ Δ · φ →
              ---------------
              Γ ⊢ Δ · φ ⇔ ψ
```

### Cut

In the last group we have the *cut rule*, which allows us to discard an assumption:

```
    cut : Γ ⊢ Δ · φ →
          Γ · φ ⊢ Ξ →
          -----------
          Γ ⊢ Δ ++ Ξ
```

## Derived rules

We can derive more general structural rules which will facilitate our life in constructing proofs.

### Permutations

!exercise(#exercise:permutations)
~~~
Generalise the exchange rules !ref(_⊢_)(exchange-left) and !ref(_⊢_)(exchange-right) in order to allow arbitrary permutations of formulas:

```
perm-left : Perm Γ Δ →
            Γ ⊢ Ξ →
            ----------
            Δ ⊢ Ξ

perm-right : Perm Δ Ξ →
             Γ ⊢ Δ →
             ----------
             Γ ⊢ Ξ
```

*Hint*: It will be necessary to prove a further generalisation of !ref(perm-left) and !ref(perm-right) in order to make their statements inductive.
~~~
~~~
It is crucial to generalise the context for the induction to go through.

```
perm-left1 : ∀ Ψ → Perm Γ Δ →
             Ψ ++ Γ ⊢ Ξ →
             ----------------
             Ψ ++ Δ ⊢ Ξ

perm-left1 _ stop Ψ++Γ⊢Ξ = Ψ++Γ⊢Ξ
perm-left1 {φ ∷ Γ} {φ ∷ Δ} {Ξ} Ψ (skip π) ΨφΓ⊢Ξ
    rewrite ++-middle Ψ φ Δ = perm-left1 (Ψ ++ [ φ ]) π have where

    have : (Ψ ++ [ φ ]) ++ Γ ⊢ Ξ
    have rewrite sym (++-middle Ψ φ Γ) = ΨφΓ⊢Ξ

perm-left1 {φ ∷ ψ ∷ Γ} {ψ ∷ φ ∷ Δ} {Ξ} Ψ (swap π) ΨφψΓ⊢Ξ
    with exchange-left Ψ ΨφψΓ⊢Ξ
... | ΨψφΓ⊢Ξ = goal where

    have : (Ψ ++ [ ψ φ ]) ++ Γ ⊢ Ξ
    have rewrite sym (assoc-++ Ψ ([ ψ φ ]) Γ) = ΨψφΓ⊢Ξ

    goal : Ψ ++ [ ψ φ ] ++ Δ ⊢ Ξ
    goal rewrite sym (assoc-++ Ψ ([ ψ φ ]) Δ) = perm-left1 (Ψ ++ [ ψ φ ]) π have

perm-left1 {Γ} {Δ} {Ξ} Ψ (tran {bs = Θ} π ρ) Ψ++Γ⊢Ξ = perm-left1 Ψ ρ (perm-left1 Ψ π Ψ++Γ⊢Ξ)
```

With the generalised !ref(perm-left1) in hand, the proof of !ref(perm-left) is just as expected:

```
perm-left = perm-left1 ∅
```

The proof for permutations on the right is analogous.

```
perm-right1 : ∀ Ψ →
              Perm Δ Ξ →
              Γ ⊢ Ψ ++ Δ →
              ------------
              Γ ⊢ Ψ ++ Ξ

perm-right1 {Δ} {Δ} {Γ} Ψ stop Γ⊢Ψ++Δ = Γ⊢Ψ++Δ

perm-right1 {(φ ∷ Δ)} {(φ ∷ Ξ)} {Γ} Ψ (skip π) Γ⊢Ψ++Δ
    rewrite ++-middle Ψ φ Ξ = perm-right1 (Ψ ++ [ φ ]) π have where

    have : Γ ⊢ (Ψ ++ [ φ ]) ++ Δ
    have rewrite sym (++-middle Ψ φ Δ) = Γ⊢Ψ++Δ

perm-right1 {φ ∷ ψ ∷ Δ} {ψ ∷ φ ∷ Ξ} {Γ} Ψ (swap π) Γ⊢ΨφψΔ
    with exchange-right {Ψ} Γ Γ⊢ΨφψΔ
... | Γ⊢ΨψφΔ = goal where

    have : Γ ⊢ (Ψ ++ [ ψ φ ]) ++ Δ
    have rewrite sym (assoc-++ Ψ ([ ψ φ ]) Δ) = Γ⊢ΨψφΔ

    goal : Γ ⊢ Ψ ++ [ ψ φ ] ++ Ξ
    goal rewrite sym (assoc-++ Ψ ([ ψ φ ]) Ξ) = perm-right1 (Ψ ++ [ ψ φ ]) π have

perm-right1 {Δ} {Ξ} {Γ} Ψ (tran π ρ) = perm-right1 Ψ ρ ∘ perm-right1 Ψ π 

perm-right = perm-right1 ∅
```
~~~

### Weakening

!exercise(#exercise:weakening)
~~~

Generalise the weakening rules in order to allow an arbitrary super-sequence of formulas.
Proceed in three steps:

1 - In the first step, show how to extend the sequent with a list of formulas: 

```
weakening-left-++ : Γ ⊢ Δ →
                    ----------
                    Γ ++ Ξ ⊢ Δ
```

2 - In the second step, show the following more general statement:

```
weakening-left-⊑2 : ∀ Ψ →
                    Ψ ++ Γ ⊢ Ξ →
                    Γ ⊑ Δ →
                    ------------
                    Ψ ++ Δ ⊢ Ξ
```

3 - Derive the generalised weakening rule by specialising the one from the previous step:

```
weakening-left-⊑ : Γ ⊢ Ξ →
                   Γ ⊑ Δ →
                   -------
                   Δ ⊢ Ξ

instance
    inst-weakening-left-⊑ : {{Γ ⊢ Ξ}} → {{Γ ⊑ Δ}} → Δ ⊢ Ξ
    inst-weakening-left-⊑ {{x}} {{y}} = weakening-left-⊑ x y
```

The workflow for the corresponding right rules is analogous,
eventually leading to the following derived rule:

```
weakening-right-⊑ : Γ ⊢ Δ →
                    Δ ⊑ Ξ →
                    -------
                    Γ ⊢ Ξ

instance
    inst-weakening-right-⊑ : {{Γ ⊢ Δ}} → {{Δ ⊑ Ξ}} → Γ ⊢ Ξ
    inst-weakening-right-⊑ {{x}} {{y}} = weakening-right-⊑ x y
```
~~~
~~~

```
weakening-left-++ {Γ} {Δ} {Ξ = ε} Γ⊢Δ rewrite ++ε Γ = Γ⊢Δ
weakening-left-++ {Γ} {Δ} {Ξ = ξ ∷ Ξ} Γ⊢Δ =
    BEGIN
        have Γ ++ Ξ ⊢ Δ             by weakening-left-++ Γ⊢Δ
        have ξ ∷ Γ ++ Ξ ⊢ Δ         apply weakening-left at here
        have Perm (ξ ∷ Γ ++ Ξ)
                  (Γ ++ ξ ∷ Ξ)      by perm-middle Γ
        have Γ ++ ξ ∷ Ξ ⊢ Δ         apply perm-left at here , back 1
    END
```

```
weakening-left-⊑2 {.ε} {Ξ} {Δ} Ψ Γ⊢Ξ stop rewrite ++ε Ψ = weakening-left-++ Γ⊢Ξ

weakening-left-⊑2 {φ ∷ Γ} {Ξ} {φ ∷ Δ} Ψ Γ·φ⊢Ξ (match Γ⊑Δ)
    rewrite ++-middle Ψ φ Δ |
            ++-middle Ψ φ Γ = weakening-left-⊑2 (Ψ ++ [ φ ]) Γ·φ⊢Ξ Γ⊑Δ

weakening-left-⊑2 {Γ} {Ξ} {φ ∷ Δ} Ψ Γ⊢Ξ (skip Γ⊑Δ) =
    BEGIN
    have Ψ ++ Δ ⊢ Ξ             by weakening-left-⊑2 Ψ Γ⊢Ξ Γ⊑Δ
    have φ ∷ Ψ ++ Δ ⊢ Ξ         apply weakening-left at here
    have Ψ ++ φ ∷ Δ ⊢ Ξ         apply perm-left (perm-middle Ψ) at here
    END
```

```
weakening-left-⊑ = weakening-left-⊑2 ε
```

```
weakening-right-++ : Γ ⊢ Δ →
                    ----------
                    Γ ⊢ Δ ++ Ξ

weakening-right-++ {Γ} {Δ} {ε} Γ⊢Δ rewrite ++ε Δ = Γ⊢Δ
weakening-right-++ {Γ} {Δ} {ξ ∷ Ξ} Γ⊢Δ =
    BEGIN
        have Γ ⊢ Δ ++ Ξ                     by weakening-right-++ Γ⊢Δ
        have Γ ⊢ ξ ∷ Δ ++ Ξ                 apply weakening-right at here
        have Perm (ξ ∷ Δ ++ Ξ) (Δ ++ ξ ∷ Ξ) by perm-middle Δ
        have Γ ⊢ Δ ++ ξ ∷ Ξ                 apply perm-right at here , back 1
    END
```

```
weakening-right-⊑2 : ∀ Ψ →
                     Γ ⊢ Ψ ++ Δ →
                     Δ ⊑ Ξ →
                     ------------
                     Γ ⊢ Ψ ++ Ξ

weakening-right-⊑2 {Γ} {ε} {Ξ} Ψ Γ⊢Δ stop rewrite ++ε Ψ = weakening-right-++ Γ⊢Δ

weakening-right-⊑2 {Γ} {φ ∷ Δ} {φ ∷ Ξ} Ψ Γ⊢Δ·φ (match Δ⊑Ξ)
    rewrite ++-middle Ψ φ Δ |
            ++-middle Ψ φ Ξ = weakening-right-⊑2 (Ψ ++ [ φ ]) Γ⊢Δ·φ Δ⊑Ξ

weakening-right-⊑2 {Γ} {Δ} {φ ∷ Ξ} Ψ Γ⊢Δ (skip Δ⊑Ξ) =
    BEGIN
    have Γ ⊢ Ψ ++ Ξ             by weakening-right-⊑2 Ψ Γ⊢Δ Δ⊑Ξ
    have Γ ⊢ φ ∷ Ψ ++ Ξ         apply weakening-right at here
    have Γ ⊢ Ψ ++ φ ∷ Ξ         apply perm-right (perm-middle Ψ) at here
    END
```

```
weakening-right-⊑ = weakening-right-⊑2 ε
```
~~~

### General axiom

!exercise(#exercise:axiom)
~~~
The axiom rule !ref(_⊢_)(Ax) allows us to derive a sequent of the form `[ φ ] ⊢ [ φ ]`.
Show how to derive the following generalisation:

```
Ax-left-SC_ : φ ∈ Γ →
              ---------
              Γ ⊢ [ φ ]
```

*Hint*: It can be convenient to leverage on the generalised (left) weakening rule.
~~~
~~~
```
Ax-left-SC_ {Γ = φ ∷ Ξ} here = weakening-left-++ Ax
Ax-left-SC_ (there φ∈Γ) = weakening-left (Ax-left-SC φ∈Γ)
```
~~~

# Sequent calculus vs. natural deduction

In this section we compare sequent calculus and natural deduction.
In particular, we show that proof in natural deduction can be simulated in sequent calculus, and vice-versa.

For clarity, in this section we will be using `⊢SC` to denote sequent calculus proofs and `⊢ND` for natural deduction proofs:

```
_⊢SC_ = _⊢_
```

## From natural deduction to sequent calculus

We simulate natural deduction with sequent calculus.
The non-trivial cases are the eliminations.
This is where the !ref(_⊢_)(cut) rule is used.

```
ND→SC : Γ ⊢ND φ →
        -----------
        Γ ⊢SC [ φ ]
        
ND→SC (Ass φ∈Γ) = Ax-left-SC φ∈Γ

ND→SC ⊤I = weakening-left-++ ⊤-right

ND→SC (⇒I Γ·φ⊢NDψ)
    with ND→SC Γ·φ⊢NDψ
... | Γ·φ⊢ψ = ⇒-right Γ·φ⊢ψ

-- non-trivial case
ND→SC {Γ} {ψ} (⇒E {φ = φ} Γ⊢NDφ⇒ψ Γ⊢NDφ)
    with ND→SC Γ⊢NDφ⇒ψ | ND→SC Γ⊢NDφ
... | Γ⊢φ⇒ψ | Γ⊢φ =
    BEGIN
    have [ ψ ] ⊢ [ ψ ]      by Ax
    have Γ · ψ ⊢ [ ψ ]      apply weakening-left-++ at here
    have Γ ⊢ [ φ ]          by Γ⊢φ
    have Γ · φ ⇒ ψ ⊢ [ ψ ]  apply ⇒-left at here , back 1
    have Γ ⊢ [ (φ ⇒ ψ) ]    by Γ⊢φ⇒ψ
    have Γ ⊢ [ ψ ]          apply cut at here , back 1 -- cut!
    END

ND→SC (∧I Γ⊢NDφ Γ⊢NDψ)
    with ND→SC Γ⊢NDφ | ND→SC Γ⊢NDψ
... | Γ⊢φ | Γ⊢ψ = ∧-right Γ⊢φ Γ⊢ψ

ND→SC {Γ} {φ} (∧E-left {ψ = ψ} Γ⊢NDφ∧ψ)
    with ND→SC Γ⊢NDφ∧ψ
... | Γ⊢φ∧ψ =
    BEGIN
    have Γ · φ · ψ ⊢ [ φ ]      by Ax-left-SC back 1
    have Γ · φ ∧ ψ ⊢ [ φ ]      apply ∧-left at here
    have Γ ⊢ [ (φ ∧ ψ) ]        by Γ⊢φ∧ψ
    have Γ ⊢ [ φ ]              apply cut at here , back 1 -- cut!
    END

ND→SC {Γ} {ψ} (∧E-right {φ = φ} Γ⊢NDφ∧ψ)
    with ND→SC Γ⊢NDφ∧ψ
... | Γ⊢φ∧ψ =
    BEGIN
    have Γ · φ · ψ ⊢ [ ψ ]      by Ax-left-SC here
    have Γ · φ ∧ ψ ⊢ [ ψ ]      apply ∧-left at here
    have Γ ⊢ [ (φ ∧ ψ) ]        by Γ⊢φ∧ψ
    have Γ ⊢ [ ψ ]              apply cut at here , back 1 -- cut!
    END

ND→SC {Γ} {φ ∨ ψ} (∨I-left Γ⊢NDφ)
    with ND→SC Γ⊢NDφ
... | Γ⊢φ =
    BEGIN
    have Γ ⊢ [ φ ]          by Γ⊢φ
    have Γ ⊢ ∅ · φ · ψ      apply weakening-right at here
    have Γ ⊢ [ (φ ∨ ψ) ]    apply ∨-right at here
    END

ND→SC {Γ} {φ ∨ ψ} (∨I-right Γ⊢NDψ)
    with ND→SC Γ⊢NDψ
... | Γ⊢ψ =
    BEGIN
    have Γ ⊢ [ ψ ]          by Γ⊢ψ
    have [ ψ ] ⊑ ∅ · φ · ψ  by match stop -- can we mechanise this check? (subsequence of two given finite lists)
    have Γ ⊢ ∅ · φ · ψ      apply weakening-right-⊑ at back 1 , here
    have Γ ⊢ [ (φ ∨ ψ) ]    apply ∨-right at here
    END

ND→SC (∨E {Γ} {φ} {ψ} {θ} Γ⊢NDφ∨ψ Γ·φ⊢NDθ Γ·ψ⊢NDθ)
    with ND→SC Γ⊢NDφ∨ψ | ND→SC Γ·φ⊢NDθ | ND→SC Γ·ψ⊢NDθ
... | Γ⊢φ∨ψ | Γ·φ⊢θ | Γ·ψ⊢θ = 
    BEGIN
    have Γ · φ ⊢ [ θ ]          by Γ·φ⊢θ
    have Γ · ψ ⊢ [ θ ]          by Γ·ψ⊢θ
    have Γ · φ ∨ ψ ⊢ [ θ ]      apply ∨-left at back 1 , here
    have Γ ⊢ [ (φ ∨ ψ) ]        by Γ⊢φ∨ψ
    have Γ ⊢ [ θ ]              apply cut at here , back 1 -- cut!
    END

ND→SC {Γ} {φ} (⊥E Γ⊢ND⊥)
    with ND→SC Γ⊢ND⊥
... | Γ⊢⊥ =
    BEGIN
    have [ ⊥ ] ⊢ ∅         by ⊥-left
    have [ ⊥ ] ⊢ [ φ ]     apply weakening-right at here
    have Γ · ⊥ ⊢ [ φ ]     apply weakening-left-++ at here
    have Γ ⊢ [ ⊥ ]         by Γ⊢⊥
    have Γ ⊢ [ φ ]         apply cut at here , back 1
    END

ND→SC {Γ} {φ} (⊥⊥E Γ⊢NDφ⇒⊥⇒⊥)
    with ND→SC Γ⊢NDφ⇒⊥⇒⊥
... | Γ⊢φ⇒⊥⇒⊥ =
    BEGIN
    have [ φ ] ⊢ [ φ ]                  by Ax
    have Γ · φ ⊢ [ φ ]                  apply weakening-left-++ at here
    have Γ · φ ⊢ ∅ · φ · ⊥             apply weakening-right at here
    have Γ ⊢ ∅ · φ · φ ⇒ ⊥             apply ⇒-right at here

    have [ ⊥ ] ⊢ ∅                    by ⊥-left
    have [ ⊥ ] ⊢ [ φ ]                apply weakening-right at here
    have Γ · ⊥ ⊢ [ φ ]                apply weakening-left-++ at here
    have Γ · (φ ⇒ ⊥) ⇒ ⊥ ⊢ ∅ · φ · φ  apply ⇒-left at back 3 , here
    have Γ · (φ ⇒ ⊥) ⇒ ⊥ ⊢ [ φ ]      apply contraction-right at here
    have Γ ⊢ [ ((φ ⇒ ⊥) ⇒ ⊥) ]        by Γ⊢φ⇒⊥⇒⊥
    have Γ ⊢ [ φ ]                     apply cut at here , back 1
    END

ND→SC {Γ} {¬ φ} (¬I Γ⊢NDφ⇒⊥)
    with ND→SC Γ⊢NDφ⇒⊥
... | Γ⊢φ⇒⊥ =
    BEGIN
    have Γ · φ · ⊥ ⊢ ∅              by weakening-left-++ ⊥-left
    have Γ · φ ⊢ [ φ ]              by weakening-left-++ Ax
    have Γ · φ · φ ⇒ ⊥ ⊢ ∅          apply ⇒-left at here , back 1
    have Γ ⊢ [ (φ ⇒ ⊥) ]            by Γ⊢φ⇒⊥
    have Γ · φ ⊢ [ (φ ⇒ ⊥) ]        apply weakening-left at here

    have Γ · φ ⊢ ∅                  apply cut at here , back 2
    have Γ ⊢ [ (¬ φ) ]              apply ¬-right at here
    END

ND→SC {Γ} {φ ⇒ ⊥} (¬E Γ⊢ND¬φ)
    with ND→SC Γ⊢ND¬φ
... | Γ⊢¬φ =
    BEGIN
    have Γ · φ ⊢ [ φ ]            by Ax-left-SC here
    have [ φ ] ⊑ ∅ · ⊥ · φ        by match stop -- can this be automated?
    have Γ · φ ⊢ ∅ · ⊥ · φ        apply weakening-right-⊑ at back 1 , here
    have Γ · φ · ¬ φ ⊢ [ ⊥ ]      apply ¬-left at here
    have Γ ⊢ [ (¬ φ) ]            by Γ⊢¬φ
    have Γ · φ ⊢ [ (¬ φ) ]        apply weakening-left at here
    have Γ · φ ⊢ [ ⊥ ]            apply cut at here , back 2
    have Γ ⊢ [ (φ ⇒ ⊥) ]          apply ⇒-right at here
    END

ND→SC {Γ} {φ ⇔ ψ} (⇔I Γ⊢NDφ⇒ψ∧ψ⇒φ)
    with ND→SC Γ⊢NDφ⇒ψ∧ψ⇒φ
... | Γ⊢φ⇒ψ∧ψ⇒φ =
    BEGIN
    have Γ ⊢ [ ((φ ⇒ ψ) ∧ (ψ ⇒ φ)) ]        by Γ⊢φ⇒ψ∧ψ⇒φ
    have Γ · φ ⊢ [ ((φ ⇒ ψ) ∧ (ψ ⇒ φ)) ]    apply weakening-left at here

    have Γ · φ  ⊢ [ φ ]                     by Ax-left-SC here
    have Γ · φ · ψ ⊢ [ ψ ]                  by Ax-left-SC here
    have Γ · φ · φ ⇒ ψ ⊢ [ ψ ]              apply ⇒-left at back 1 , here
    have Γ · φ · φ ⇒ ψ · ψ ⇒ φ ⊢ [ ψ ]      apply weakening-left at here
    have Γ · φ · (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⊢ [ ψ ]  apply ∧-left at here

    have Γ · φ ⊢ [ ψ ]                      apply cut at back 5 , here

    have Γ · ψ ⊢ [ ((φ ⇒ ψ) ∧ (ψ ⇒ φ)) ]    apply weakening-left at back 7

    have Γ · ψ ⊢ [ ψ ]                      by Ax-left-SC here
    have Γ · ψ · φ ⇒ ψ ⊢ [ ψ ]              apply weakening-left at here
    have Γ · ψ · φ ⇒ ψ · φ ⊢ [ φ ]          by Ax-left-SC here

    have Γ · ψ · φ ⇒ ψ · ψ ⇒ φ ⊢ [ φ ]      apply ⇒-left at back 1 , here
    have Γ · ψ · (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⊢ [ φ ]  apply ∧-left at here
    have Γ · ψ ⊢ [ φ ]                      apply cut at back 5 , here

    have Γ ⊢ [ (φ ⇔ ψ) ]                    apply ⇔-right at back 7 , here
    END

ND→SC {Γ} {(φ ⇒ ψ) ∧ (ψ ⇒ φ)} (⇔E Γ⊢NDφ⇔ψ)
    with ND→SC Γ⊢NDφ⇔ψ
... | Γ⊢φ⇔ψ =
    BEGIN
    have Γ ⊢ [ (φ ⇔ ψ) ]                    by Γ⊢φ⇔ψ
    have Γ · φ ⊢ [ (φ ⇔ ψ) ]                apply weakening-left at here
    have Γ · φ ⊢ ∅ · φ · ψ                  by weakening-right (Ax-left-SC here)
    have Γ · φ · φ · ψ ⊢ [ ψ ]              by Ax-left-SC here
    have Γ · φ · φ ⇔ ψ ⊢ [ ψ ]              apply ⇔-left at back 1 , here
    have Γ · φ ⊢ [ ψ ]                      apply cut at back 3 , here
    have Γ ⊢ [ (φ ⇒ ψ) ]                    apply ⇒-right at here

    have Γ · ψ ⊢ [ (φ ⇔ ψ) ]                apply weakening-left at back 6
    have Γ · ψ ⊢ ∅ · φ · ψ                  by weakening-right-⊑ (Ax-left-SC here) (match stop)
    have Γ · ψ · φ · ψ ⊢ [ φ ]              by weakening-left (Ax-left-SC here)
    have Γ · ψ · φ ⇔ ψ ⊢ [ φ ]              apply ⇔-left at back 1 , here
    have Γ · ψ ⊢ [ φ ]                      apply cut at back 3 , here
    have Γ ⊢ [ (ψ ⇒ φ) ]                    apply ⇒-right at here

    have Γ ⊢ [ ((φ ⇒ ψ) ∧ (ψ ⇒ φ)) ]        apply ∧-right at back 6 , here
    END
```

## From sequent calculus to natural deduction

We simulate sequent calculus with natural deduction.
Since natural deduction takes a single formula on the right,
we take the disjunction of all formulas of the right half of a sequent.

```
SC→ND : Γ ⊢SC Δ →
        -----------
        Γ ⊢ND ⋁ Δ

SC→ND Ax = Ass here

SC→ND (weakening-left Γ⊢Δ)
    with SC→ND Γ⊢Δ
... | Γ⊢NDΔ = weakening-ND Γ⊢NDΔ there

SC→ND {Γ} {φ ∷ Δ} (weakening-right Γ⊢Δ)
    with SC→ND Γ⊢Δ
... | Γ⊢NDΔ
    with Δ 
... | ε = ⊥E Γ⊢NDΔ
... | _ ∷ _ = ∨I-right Γ⊢NDΔ

SC→ND (exchange-left {φ} {ψ} {Δ} {Ξ} Γ ΓφψΔ⊢Ξ)
    with SC→ND ΓφψΔ⊢Ξ 
... | ΓφψΔ⊢NDΞ = perm-ND-left (swap-deep Γ) ΓφψΔ⊢NDΞ

SC→ND (exchange-right {Δ} {φ} {ψ} {Ξ} Γ Γ⊢ΔφψΞ)
    with SC→ND Γ⊢ΔφψΞ
... | Γ⊢NDΔφψΞ = perm-ND-right (swap-deep Δ) Γ⊢NDΔφψΞ

SC→ND (contraction-left Γφφ⊢Δ)
    with SC→ND Γφφ⊢Δ
... | Γφφ⊢NDΔ = contraction-ND-left Γφφ⊢NDΔ

SC→ND {Δ = φ ∷ Δ} (contraction-right Γ⊢Δφφ)
    with SC→ND Γ⊢Δφφ
... | Γ⊢NDΔφφ = contraction-ND-right Δ Γ⊢NDΔφφ

SC→ND ⊥-left = Ass here

SC→ND ⊤-right = ⊤I

SC→ND (¬-left {Γ} {Δ} {φ} Γ⊢Δ·φ)
    with SC→ND Γ⊢Δ·φ
... | Γ⊢NDΔ∨φ
    with Δ
... | ε =
    BEGIN
    have Γ ⊢ND φ            by Γ⊢NDΔ∨φ
    have Γ ⊆ Γ · ¬ φ        by there
    have Γ · ¬ φ ⊢ND φ      apply weakening-ND at back 1 , here
    have Γ · ¬ φ ⊢ND ¬ φ    by Ass here
    have Γ · ¬ φ ⊢ND φ ⇒ ⊥  apply ¬E at here
    have Γ · ¬ φ ⊢ND ⊥      apply ⇒E at here , back 2
    END

... | Ξ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND φ ∨ (⋁ Ξ)            by Γ⊢NDΔ∨φ
    have Γ ⊆ Γ · ¬ φ                by there
    have Γ · ¬ φ ⊢ND φ ∨ (⋁ Ξ)      apply weakening-ND at back 1 , here

    have Γ · ¬ φ · φ ⊢ND φ          by Ass here
    have Γ · ¬ φ · φ ⊢ND ¬ φ        by Ass back 1
    have Γ · ¬ φ · φ ⊢ND φ ⇒ ⊥      apply ¬E at here
    have Γ · ¬ φ · φ ⊢ND ⊥          apply ⇒E at here , back 2

    have Γ · ¬ φ · φ ⊢ND ⋁ Ξ        apply ⊥E at here

    have Γ · ¬ φ · (⋁ Ξ) ⊢ND ⋁ Ξ    by Ass here

    have Γ · ¬ φ ⊢ND ⋁ Ξ            apply ∨E at back 6 , back 1 , here
    END

SC→ND (¬-right {Γ} {φ} {Δ} Γ·φ⊢Δ)
    with SC→ND Γ·φ⊢Δ
... | Γ·φ⊢ND⋁Δ
    with Δ
... | ε =
    BEGIN
    have Γ · φ ⊢ND ⊥    by Γ·φ⊢ND⋁Δ
    have Γ ⊢ND φ ⇒ ⊥    apply ⇒I at here
    have Γ ⊢ND ¬ φ      apply ¬I at here
    END

... | Ξ@(_ ∷ _) =
    BEGIN
    have Γ · φ ⊢ND ⋁ Ξ                      by Γ·φ⊢ND⋁Δ
    have Γ · φ ⊢ND ¬ φ ∨ (⋁ Ξ)              apply ∨I-right at here
    
    have Γ · φ ⇒ ⊥ ⊢ND φ ⇒ ⊥                by Ass here 
    have Γ · φ ⇒ ⊥ ⊢ND ¬ φ                  apply ¬I at here
    have Γ · φ ⇒ ⊥ ⊢ND ¬ φ ∨ (⋁ Ξ)          apply ∨I-left at here
    
    have Γ ⊢ND ¬ φ ∨ (⋁ Ξ)                  apply case-split at back 3 , here 
    END

SC→ND (∧-left {Γ} {φ} {ψ} {Δ} Γφψ⊢Δ)
    with SC→ND Γφψ⊢Δ
... | Γφψ⊢ND⋁Δ = ∧-left-ND Γφψ⊢ND⋁Δ

SC→ND (∧-right {Γ} {Δ} {φ} {ψ} Γ⊢Δ·φ Γ⊢Δ·ψ)
    with SC→ND Γ⊢Δ·φ | SC→ND Γ⊢Δ·ψ
... | Γ⊢ND⋁Δφ | Γ⊢ND⋁Δψ
    with Δ
... | ε =
    BEGIN
    have Γ ⊢ND φ            by Γ⊢ND⋁Δφ
    have Γ ⊢ND ψ            by Γ⊢ND⋁Δψ
    have Γ ⊢ND φ ∧ ψ        apply ∧I at back 1 , here
    END

... | Ξ@(_ ∷ _ ) =
    BEGIN
    have Γ ⊢ND φ ∨ (⋁ Ξ)                        by Γ⊢ND⋁Δφ
    have Γ · (⋁ Ξ) ⇒ ⊥ ⊢ND φ                    apply swap-Neg-Or-ND at here

    have Γ ⊢ND ψ ∨ (⋁ Ξ)                        by Γ⊢ND⋁Δψ
    have Γ · (⋁ Ξ) ⇒ ⊥ ⊢ND ψ                    apply swap-Neg-Or-ND at here

    have Γ · (⋁ Ξ) ⇒ ⊥ ⊢ND φ ∧ ψ                apply ∧I at back 2 , here
    have Γ · (⋁ Ξ) ⇒ ⊥ ⊢ND φ ∧ ψ ∨ (⋁ Ξ)        apply ∨I-left at here

    have Γ · (⋁ Ξ) ⊢ND ⋁ Ξ                      by Ass here
    have Γ · (⋁ Ξ) ⊢ND φ ∧ ψ ∨ (⋁ Ξ)            apply ∨I-right at here

    have Γ ⊢ND φ ∧ ψ ∨ (⋁ Ξ)                    apply case-split at here , back 2
    END

SC→ND (∨-left {Γ} {φ} {Δ} {ψ} Γ·φ⊢Δ Γ·ψ⊢Δ)
    with SC→ND Γ·φ⊢Δ | SC→ND Γ·ψ⊢Δ
... | Γ·φ⊢ND⋁Δ | Γ·ψ⊢ND⋁Δ = ∨-left-ND Γ·φ⊢ND⋁Δ Γ·ψ⊢ND⋁Δ

SC→ND (∨-right {Γ} {Δ} {φ} {ψ} Γ⊢Δ·φ·ψ)
    with SC→ND Γ⊢Δ·φ·ψ
... | Γ⊢NDΔ·φ·ψ
    with Δ
... | ε = ⇒E commOr-ND Γ⊢NDΔ·φ·ψ

... | Ξ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND ψ ∨ φ ∨ (⋁ Ξ)                        by Γ⊢NDΔ·φ·ψ
    have Γ ⊢ND (ψ ∨ φ) ∨ (⋁ Ξ)                      apply assocOr-ND at here
    have Γ ⊢ND (ψ ∨ φ) ⇒ (φ ∨ ψ)                    by commOr-ND
    have Γ ⊢ND (φ ∨ ψ) ∨ (⋁ Ξ)                      apply attachOr-ND at back 1 , here
    END

SC→ND (⇒-left {Γ} {Δ} {φ} {ψ} {Ξ} Γ⊢Δ·φ Γ·ψ⊢Ξ)
    with SC→ND Γ⊢Δ·φ | SC→ND Γ·ψ⊢Ξ
... | Γ⊢NDΔ·φ | Γ·ψ⊢NDΞ
    with Δ
... | ε =
    BEGIN
    have Γ ⊢ND φ                    by Γ⊢NDΔ·φ
    have Γ ⊆ Γ · φ ⇒ ψ              by there
    have Γ · φ ⇒ ψ ⊢ND φ            apply weakening-ND at back 1 , here
    have Γ · φ ⇒ ψ ⊢ND φ ⇒ ψ        by Ass here
    have Γ · φ ⇒ ψ ⊢ND ψ            apply ⇒E at here , back 1

    have Γ · ψ ⊢ND ⋁ Ξ              by Γ·ψ⊢NDΞ
    have Γ ⊢ND ψ ⇒ (⋁ Ξ)            apply DT2-ND at here
    have Γ · φ ⇒ ψ ⊢ND ψ ⇒ (⋁ Ξ)    apply weakening-ND at here , back 5
    have Γ · φ ⇒ ψ ⊢ND ⋁ Ξ          apply ⇒E at here , back 3
    END
    
... | Ψ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND φ ∨ (⋁ Ψ)                    by Γ⊢NDΔ·φ
    have Γ · ψ ⊢ND ⋁ Ξ                      by Γ·ψ⊢NDΞ
    have Γ · φ ⇒ ψ ⊢ND (⋁ Ψ) ∨ (⋁ Ξ)        apply ⇒-left-ND at back 1 , here
    have Γ · φ ⇒ ψ ⊢ND ⋁ (Ψ ++ Ξ)           apply longDisjunction-++-ND Ψ at here
    END

SC→ND (⇒-right {Γ} {φ} {Δ} {ψ} Γ·φ⊢Δ·ψ)
    with SC→ND Γ·φ⊢Δ·ψ
... | Γ·φ⊢NDΔ·ψ
    with Δ
... | ε = ⇒I Γ·φ⊢NDΔ·ψ
... | Ψ@(_ ∷ _) = ⇒-right-ND Γ·φ⊢NDΔ·ψ

SC→ND (⇔-left {Γ} {Δ} {φ} {ψ} {Ξ} Γ⊢Δ·φ·ψ Γ·φ·ψ⊢Ξ)
    with SC→ND Γ⊢Δ·φ·ψ | SC→ND Γ·φ·ψ⊢Ξ
... | Γ⊢NDΔ·φ·ψ | Γ·φ·ψ⊢NDΞ
    with Δ
... | ε = ⇔-left-ND Γ⊢NDΔ·φ·ψ Γ·φ·ψ⊢NDΞ

... | Ψ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND ψ ∨ φ ∨ (⋁ Ψ)                by Γ⊢NDΔ·φ·ψ
    have Γ · φ · ψ ⊢ND ⋁ Ξ                  by Γ·φ·ψ⊢NDΞ
    have Γ · φ ⇔ ψ ⊢ND (⋁ Ψ) ∨ (⋁ Ξ)        apply ⇔-left'-ND at back 1 , here
    have Γ · φ ⇔ ψ ⊢ND ⋁ (Ψ ++ Ξ)           apply longDisjunction-++-ND Ψ at here
    END

SC→ND (⇔-right {Γ} {φ} {Δ} {ψ} Γ·φ⊢Δ·ψ Γ·ψ⊢Δ·φ)
    with SC→ND Γ·φ⊢Δ·ψ | SC→ND Γ·ψ⊢Δ·φ
... | Γ·φ⊢NDΔ·ψ | Γ·ψ⊢NDΔ·φ
    with Δ
... | ε = ↔-right-ND Γ·φ⊢NDΔ·ψ Γ·ψ⊢NDΔ·φ

... | Ψ@(_ ∷ _) = ↔-right'-ND Γ·φ⊢NDΔ·ψ Γ·ψ⊢NDΔ·φ

SC→ND (cut {Γ} {Δ} {φ} {Ξ} Γ⊢Δ·φ Γ·φ⊢Ξ)
    with SC→ND Γ⊢Δ·φ | SC→ND Γ·φ⊢Ξ
... | Γ⊢NDΔ·φ | Γ·φ⊢NDΞ
    with Δ
... | ε =
    BEGIN
    have Γ ⊢ND φ            by Γ⊢NDΔ·φ
    have Γ · φ ⊢ND ⋁ Ξ      by Γ·φ⊢NDΞ
    have Γ ⊢ND φ ⇒ (⋁ Ξ)    apply ⇒I at here
    have Γ ⊢ND ⋁ Ξ          apply ⇒E at here , back 2
    END

... | Ψ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND φ ∨ (⋁ Ψ)           by Γ⊢NDΔ·φ
    have Γ · φ ⊢ND ⋁ Ξ             by Γ·φ⊢NDΞ
    have Γ ⊢ND (⋁ Ψ) ∨ (⋁ Ξ)       apply cut-ND at back 1 , here
    have Γ ⊢ND ⋁ (Ψ ++ Ξ)          apply longDisjunction-++-ND Ψ at here
    END
```

# Soundness and completeness

Thanks to the mutual translations from and to natural deduction and thanks to the fact that natural deduction is sound and complete,
we obtain that also sequent calculus is sound and complete:

```
soundness-SC : Γ ⊢ Δ →
               --------
               Γ ⊨ ⋁ Δ

soundness-SC Γ⊢Δ = soundness-ND (SC→ND Γ⊢Δ)
```

```
completeness-SC : Γ ⊨ φ →
                  ---------
                  Γ ⊢ [ φ ]

completeness-SC Γ⊨⋁Δ = ND→SC (completeness-ND Γ⊨⋁Δ)
```

# Cut elimination

```
-- mix : Γ₀ ⊢ Δ₀ · φ →
--       Γ₁ · φ ⊢ Δ₁ →
--       -------------------
--       Γ₀ ++ Γ₁ ⊢ Δ₀ ++ Δ₁

-- mix = {!   !}
```

```

```

The *degree* of a derivation is the maximal size of a formula eliminated by an application of the cut rule:

```
degree : Γ ⊢ Δ → ℕ

degree (cut {φ = φ} Γ⊢Δ·φ Γ·φ⊢Ξ) = max (size φ) (max (degree Γ⊢Δ·φ) (degree Γ·φ⊢Ξ))

degree Ax = 0
degree ⊥-left = 0
degree ⊤-right = 0
degree (weakening-left Γ⊢Δ) = degree Γ⊢Δ
degree (weakening-right Γ⊢Δ) = degree Γ⊢Δ
degree (exchange-left _ Γ⊢Δ) = degree Γ⊢Δ
degree (exchange-right _ Γ⊢Δ) = degree Γ⊢Δ
degree (contraction-left Γ⊢Δ) = degree Γ⊢Δ
degree (contraction-right Γ⊢Δ) = degree Γ⊢Δ
degree (¬-left Γ⊢Δ) = degree Γ⊢Δ
degree (¬-right Γ⊢Δ) = degree Γ⊢Δ
degree (∧-left Γ⊢Δ) = degree Γ⊢Δ
degree (∧-right Γ⊢Δ Γ⊢Δ₁) = max (degree Γ⊢Δ) (degree Γ⊢Δ₁)
degree (∨-left Γ⊢Δ Γ⊢Δ₁) = max (degree Γ⊢Δ) (degree Γ⊢Δ₁)
degree (∨-right Γ⊢Δ) = degree Γ⊢Δ
degree (⇒-left Γ⊢Δ Γ⊢Δ₁) = max (degree Γ⊢Δ) (degree Γ⊢Δ₁)
degree (⇒-right Γ⊢Δ) = degree Γ⊢Δ
degree (⇔-left Γ⊢Δ Γ⊢Δ₁) = max (degree Γ⊢Δ) (degree Γ⊢Δ₁)
degree (⇔-right Γ⊢Δ Γ⊢Δ₁) = max (degree Γ⊢Δ) (degree Γ⊢Δ₁)
```

```
-- remove-add-left : ∀ φ → Γ ⊢ Δ → Γ ∖ φ · φ ⊢ Δ
-- remove-add-left = {!   !}

-- remove-add-left-degree : ∀ d φ (Γ⊢Δ : Γ ⊢ Δ) → degree Γ⊢Δ ≤ d → degree (remove-add-left φ Γ⊢Δ) ≤ d
-- remove-add-left-degree = {!   !}

-- remove-add-right : ∀ φ → Γ ⊢ Δ → Γ ⊢ Δ ∖ φ ++ [ φ ]
-- remove-add-right = {!   !}

-- remove-add-right-degree : ∀ d φ (Γ⊢Δ : Γ ⊢ Δ) → degree Γ⊢Δ ≤ d → degree (remove-add-right φ Γ⊢Δ) ≤ d
-- remove-add-right-degree = {!   !}

-- ⊥-left-mix : Γ ⊢ Δ → Γ ⊢ Δ ∖ ⊥
-- ⊥-left-mix = {!   !}

-- ⊥-left-mix-degree : ∀ d (Γ⊢Δ : Γ ⊢ Δ) → degree Γ⊢Δ ≤ d → degree (⊥-left-mix Γ⊢Δ) ≤ d
-- ⊥-left-mix-degree = {!   !}

-- ⊤-right-mix : Γ ⊢ Δ → Γ ∖ ⊤ ⊢ Δ
-- ⊤-right-mix = {!   !}

-- ⊤-right-mix-degree : ∀ d (Γ⊢Δ : Γ ⊢ Δ) → degree Γ⊢Δ ≤ d → degree (⊤-right-mix Γ⊢Δ) ≤ d
-- ⊤-right-mix-degree = {!   !}

instance deriv-equal : {{Γ ⊢ Δ}} → {{Δ ≡ Ξ}} → Γ ⊢ Ξ
deriv-equal {Γ} {{Γ⊢Δ}} {{Δ≡Ξ}} = repl Γ⊢Δ (cong (λ C → Γ ⊢ C) Δ≡Ξ)


```

```
Degree = ℕ

private
    variable
        d d₀ d₁ : Degree

infixr 5 _⊢_#_
data _⊢_#_ : Context → Context → ℕ → Set where

    Ax : [ φ ] ⊢ [ φ ] # 0
    ⊥-left : [ ⊥ ] ⊢ ∅ # 0
    ⊤-right : ∅ ⊢ [ ⊤ ] # 0

    weakening-left : Γ ⊢ Δ # d →
                     -------------
                     Γ · φ ⊢ Δ # d

    weakening-right : Γ ⊢ Δ # d →
                      -------------
                      Γ ⊢ Δ · φ # d

    exchange-left : ∀ Γ →
                    Γ ++ [ φ ψ ] ++ Δ ⊢ Ξ # d →
                    -------------------------
                    Γ ++ [ ψ φ ] ++ Δ ⊢ Ξ # d

    exchange-right : ∀ Γ →
                     Γ ⊢ Δ ++ [ φ ψ ] ++ Ξ # d →
                     -------------------------
                     Γ ⊢ Δ ++ [ ψ φ ] ++ Ξ # d

    contraction-left : Γ · φ · φ ⊢ Δ # d →
                       -------------
                       Γ · φ ⊢ Δ # d

    contraction-right : Γ ⊢ Δ · φ · φ # d →
                        -------------
                        Γ ⊢ Δ · φ # d

    ¬-left : Γ ⊢ Δ · φ # d →
             ---------------
             Γ · ¬ φ ⊢ Δ # d

    ¬-right : Γ · φ ⊢ Δ # d →
              ---------------
              Γ ⊢ Δ · ¬ φ # d

    ∧-left : Γ · φ · ψ ⊢ Δ # d →
             -----------------
             Γ · φ ∧ ψ ⊢ Δ # d

    ∧-right : Γ ⊢ Δ · φ # d →
              Γ ⊢ Δ · ψ # d →
              -------------------------
              Γ ⊢ Δ · φ ∧ ψ # d

    ∨-left : Γ · φ ⊢ Δ # d →
             Γ · ψ ⊢ Δ # d →
             -------------------------
             Γ · φ ∨ ψ ⊢ Δ # d

    ∨-right : Γ ⊢ Δ · φ · ψ # d →
              -----------------
              Γ ⊢ Δ · φ ∨ ψ # d

    ⇒-left : Γ ⊢ Δ · φ # d →
             Γ · ψ ⊢ Ξ # d →
             ------------------------------
             Γ · φ ⇒ ψ ⊢ Δ ++ Ξ # d

    ⇒-right : Γ · φ ⊢ Δ · ψ # d →
              -----------------
              Γ ⊢ Δ · φ ⇒ ψ # d

    ⇔-left : Γ ⊢ Δ · φ · ψ # d →
             Γ · φ · ψ ⊢ Ξ # d →
             ------------------------------
             Γ · φ ⇔ ψ ⊢ Δ ++ Ξ # d

    ⇔-right : Γ · φ ⊢ Δ · ψ # d →
              Γ · ψ ⊢ Δ · φ # d →
              -------------------------
              Γ ⊢ Δ · φ ⇔ ψ # d

    cut : Γ ⊢ Δ · φ # d →
          Γ · φ ⊢ Ξ # d →
          size φ ≤ d →
          -------------------------------------
          Γ ⊢ Δ ++ Ξ # d

    degree-up : Γ ⊢ Δ · φ # d₀ →
                d₀ ≤ d₁ →
                ---------------
                Γ ⊢ Δ · φ # d₁
```

```
-- weakening-left#-⊑1 : Γ ⊢ Δ # d →
--                     --------------
--                     Γ ++ Ξ ⊢ Δ # d

-- weakening-left#-⊑1 = {!   !}

contraction-left#-⊑ : Γ ++ Δ ⊢ Ξ # d →
                      Δ ⊑ Γ →
                      ----------
                      Γ ⊢ Ξ # d

contraction-left#-⊑ = {!   !}

weakening-left#-++ : Γ ⊢ Δ # d →
                    --------------
                    Γ ++ Ξ ⊢ Δ # d

weakening-left#-++ = {!   !}

weakening-right#-++ : Γ ⊢ Δ # d →
                    --------------
                    Γ ⊢ Δ ++ Ξ # d

weakening-right#-++ = {!   !}

weakening-left-right#-++ : Γ₀ ⊢ Δ₀ # d →
                    -----------------------
                    Γ₀ ++ Γ₁ ⊢ Δ₀ ++ Δ₁ # d

weakening-left-right#-++ = {!   !}

weakening-right#-⊑ : Γ ⊢ Δ # d →
                     Δ ⊑ Ξ →
                     ------------
                     Γ ⊢ Ξ # d

weakening-right#-⊑ = {!   !}

contraction-right-deep : Γ ⊢ Δ · φ · φ ++ Ξ # d →
                        --------------------------
                        Γ ⊢ Δ · φ ++ Ξ # d

contraction-right-deep = {!   !}

¬-left-deep : Γ ⊢ Δ · φ ++ Ξ # d →
             ---------------------
             Γ · ¬ φ ⊢ Δ ++ Ξ # d
            
¬-left-deep = {!   !}

remove-add-left : ∀ φ → Γ ⊢ Δ # d → Γ ∖ φ · φ ⊢ Δ # d
remove-add-left = {!   !}

remove-add-right : ∀ φ → Γ ⊢ Δ # d → Γ ⊢ Δ ∖ φ ++ [ φ ] # d
remove-add-right = {!   !}

⊥-left-mix : Γ ⊢ Δ # d → Γ ⊢ Δ ∖ ⊥ # d
⊥-left-mix = {!   !}

⊤-right-mix : Γ ⊢ Δ # d → Γ ∖ ⊤ ⊢ Δ # d
⊤-right-mix = {!   !}

mix : Γ₀ ⊢ Δ₀ · φ # d →
      Γ₁ · φ ⊢ Δ₁ # d →
      size φ ≡ 1 + d →
      -----------------------------------------
      Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d

mix' : Γ₀ ⊢ Δ₀ # d →
      Γ₁ ⊢ Δ₁ # d →
      φ ∈ Δ₀ →
      φ ∈ Γ₁ →
      size φ ≡ 1 + d →
      -----------------------------------------
      Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d

mix {Δ₀ = Δ₀} {φ = φ} {Γ₁ = Γ₁} δ₀ δ₁ sφ
    rewrite sym (remove-∷ φ Γ₁) |
            sym (remove-∷ φ Δ₀) = mix' δ₀ δ₁ here here sφ
```

* `δ₀` is !ref(_⊢_)(Ax):

```
mix' {φ = φ} Ax δ₁ here φ∈Γ₁ sφ rewrite remove-sing φ = remove-add-left φ δ₁
```

-- * `δ₁` is !ref(_⊢_)(Ax):

```
-- mix' {Γ₀ = Γ₀} {φ = φ} δ₀ Ax φ∈Δ₀ here sφ
--     rewrite remove-sing φ | ++ε Γ₀ = remove-add-right φ δ₀
```

* `δ₀` consists of !ref(_⊢_)(⊥-left) is impossible since `φ ∈ Δ₀` shows that `Δ₀` is nonempty
(this is automatically detected and we need not write this case explicitly).

-- * `δ₁` consists of !ref(_⊢_)(⊥-left). It follows that `φ ≡ ⊥`, `Γ₁ ≡ [ φ ]`, and `Δ₁ ≡ ∅`.
-- We need to show `Γ₀ ⊢ Δ₀ ∖ ⊥ # d`, which is done by the auxiliary function !ref(⊥-left-mix):

```
-- mix' {Γ₀} {Δ₀} δ₀ ⊥-left φ∈Γ₀ here sφ
--     rewrite remove-sing ⊥ | ++ε Γ₀ | ++ε (Δ₀ ∖ ⊥) = ⊥-left-mix δ₀
```

* `d₀` consists of !ref(_⊢_)(⊤-right).
In this case `Γ₀ ≡ ∅`, `Δ₀ ≡ [ ⊤ ]`, and thus `φ ≡ ⊤`.
We need to show `Γ₁ ∖ ⊤ ⊢ Δ₁ # d` which is done with the auxiliary function !ref(⊤-right-mix):

```
mix' ⊤-right δ₁ here φ∈Γ₁ sφ = ⊤-right-mix δ₁
```

```
mix' (weakening-left δ₀) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = weakening-left (mix' δ₀ δ₁ φ∈Δ₀ φ∈Γ₁ sφ)
```

```
mix' {Δ₀ = Δ₀} {d} {Γ₁} {Δ₁} {φ} (exchange-left {ψ} {ξ} {Γ₀′} {Ξ} Γ₀ δ₀) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = goal where

    ind : (Γ₀ ++ [ ψ ξ ] ++ Γ₀′) ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
    ind = mix' δ₀ δ₁ φ∈Δ₀ φ∈Γ₁ sφ

    have0 : Γ₀ ++ [ ψ ξ ] ++ Γ₀′ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
    have0 = {! ind   !}

    have1 : Γ₀ ++ [ ξ ψ ] ++ Γ₀′ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
    have1 = exchange-left Γ₀ have0

    goal : (Γ₀ ++ [ ξ ψ ] ++ Γ₀′) ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
    goal  = {!  have1 !}
```

```
mix' {Γ₀} {ψ ∷ Δ₀} {d} {Γ₁} {Δ₁} {φ} (weakening-right δ₀) δ₁ φ∈Δ₀·ψ φ∈Γ₁ sφ = goal where

    goal : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d
    goal with ∈→∈1 φ∈Δ₀·ψ
    ... | there φ≢ψ φ∈1Δ₀ = goal′ where

        ind : Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
        ind = mix' δ₀ δ₁ (∈1→∈ φ∈1Δ₀) φ∈Γ₁ sφ

        have : Γ₀ ++ Γ₁ ∖ φ ⊢ ((Δ₀ ∖ φ) · ψ) ++ Δ₁ # d
        have = weakening-right ind

        eql : Γ₀ ++ Γ₁ ∖ φ ⊢ ((Δ₀ ∖ φ) · ψ) ++ Δ₁ # d ≡ Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d
        eql rewrite remove-≢-∷ Δ₀ φ≢ψ = refl

        goal′ : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d
        goal′ = repl have eql
    
    ... | here
        rewrite remove-∷ φ Δ₀
        with φ ∈? Δ₀
    ... | yes φ∈Δ₀ = mix' δ₀ δ₁ φ∈Δ₀ φ∈Γ₁ sφ
    ... | no ~φ∈Δ₀ rewrite remove-~∈-2 ~φ∈Δ₀ =
            BEGIN
                have Γ₀ ⊢ Δ₀ # d                    by δ₀
                have Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ++ Δ₁ # d    apply weakening-left-right#-++ at here
            END
```

```
mix' {Γ₀} {_} {d} {Γ₁} {Δ₁} {φ} (exchange-right {Δ₀} {ψ} {ξ} {Δ₀′} Γ₀ δ₀) δ₁ φ∈Δ₀ξψΔ₀′ φ∈Γ₁ sφ = goal  where

    -- from φ∈Δ₀ξψΔ₀′
    φ∈Δ₀ψξΔ₀′ : φ ∈ Δ₀ ++ [ ψ ξ ] ++ Δ₀′
    φ∈Δ₀ψξΔ₀′ = {!   !}

    ind : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ ++ [ ψ ξ ] ++ Δ₀′) ∖ φ ++ Δ₁ # d
    ind = mix' δ₀ δ₁ φ∈Δ₀ψξΔ₀′ φ∈Γ₁ sφ

    eql : ∀ ψ ξ →
            ~ (φ ∈ [ ψ ξ ]) →
            Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ ++ [ ψ ξ ] ++ Δ₀′) ∖ φ ++ Δ₁ # d ≡
            Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ [ ψ ξ ] ++ Δ₀′ ∖ φ ++ Δ₁ # d
    eql ψ ξ ~φ∈[ψξ] rewrite
        remove-++ φ Δ₀ ([ ψ ξ ] ++ Δ₀′) |
        remove-++ φ ([ ψ ξ ]) Δ₀′ |
        remove-~∈-2 ~φ∈[ψξ] |
        sym (assoc-++ (Δ₀ ∖ φ) ([ ψ ξ ]) (Δ₀′ ∖ φ)) |
        assoc-++ (Δ₀ ∖ φ ++ [ ψ ξ ]) (Δ₀′ ∖ φ) Δ₁ |
        assoc-++ (Δ₀ ∖ φ) ([ ψ ξ ]) (Δ₀′ ∖ φ ++ Δ₁) = refl

    goal : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ ++ [ ξ ψ ] ++ Δ₀′) ∖ φ ++ Δ₁ # d
    goal with ψ ≡? ξ
    ... | yes refl = ind where
    ... | no  ψ≢ξ
         with φ ∈1? [ ξ ψ ]
    ... | yes here = repl ind eql′ where

        eql′ : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ ++ [ ψ ξ ] ++ Δ₀′) ∖ φ ++ Δ₁ # d ≡
              Γ₀ ++ Γ₁ ∖ ξ ⊢ (Δ₀ ++ [ ξ ψ ] ++ Δ₀′) ∖ ξ ++ Δ₁ # d
        eql′ = {!   !}

    ... | yes (there φ≢ξ here) = repl ind eql′ where

        eql′ : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ ++ [ ψ ξ ] ++ Δ₀′) ∖ φ ++ Δ₁ # d ≡
              Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ₀ ++ [ ξ ψ ] ++ Δ₀′) ∖ ψ ++ Δ₁ # d
        eql′ = {!   !}

    ... | no ~φ∈1[ξψ] = have2 where

        -- from ~φ∈1[ξψ]
        ~φ∈[ξψ] : ~ (φ ∈ [ ξ ψ ])
        ~φ∈[ξψ] = {!   !}

        ~φ∈[ψξ] : ~ (φ ∈ [ ψ ξ ])
        ~φ∈[ψξ] = {!   !}

        have0 : Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ [ ψ ξ ] ++ Δ₀′ ∖ φ ++ Δ₁ # d
        have0 rewrite sym (eql ψ ξ ~φ∈[ψξ]) = ind

        have1 : Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ [ ξ ψ ] ++ Δ₀′ ∖ φ ++ Δ₁ # d
        have1 = exchange-right {Δ₀ ∖ φ} {ψ} {ξ} _ have0

        have2 : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ ++ [ ξ ψ ] ++ Δ₀′) ∖ φ ++ Δ₁ # d
        have2 rewrite eql ξ ψ ~φ∈[ξψ] = have1
```

```
mix' (contraction-left δ₀) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = contraction-left (mix' δ₀ δ₁ φ∈Δ₀ φ∈Γ₁ sφ)
```

```
mix' {Γ₀} {ψ ∷ Δ₀} {d} {Γ₁} {Δ₁} {φ} (contraction-right δ₀) δ₁ φ∈Δ₀·ψ φ∈Γ₁ sφ = goal where

    φ∈Δ₀·ψ·ψ : φ ∈ Δ₀ · ψ · ψ
    φ∈Δ₀·ψ·ψ = {!   !}

    ind : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ · ψ) ∖ φ ++ Δ₁ # d
    ind = mix' δ₀ δ₁ φ∈Δ₀·ψ·ψ φ∈Γ₁ sφ

    goal : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d
    goal with φ ≡? ψ
    ... | yes refl = ind′ where

        eql : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · φ · φ) ∖ φ ++ Δ₁ # d ≡
              Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · φ) ∖ φ ++ Δ₁ # d
        eql rewrite remove-∷ φ (Δ₀ · φ) = refl

        ind′ : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · φ) ∖ φ ++ Δ₁ # d
        ind′ rewrite sym eql = ind

    ... | no φ≢ψ = goal′ where

        eql : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ · ψ) ∖ φ ++ Δ₁ # d ≡
              Γ₀ ++ Γ₁ ∖ φ ⊢ ((Δ₀ ∖ φ) · ψ · ψ) ++ Δ₁ # d
        eql rewrite remove-≢-∷ (Δ₀ · ψ) φ≢ψ |
                    remove-≢-∷ Δ₀ φ≢ψ = refl

        ind′ : Γ₀ ++ Γ₁ ∖ φ ⊢ ((Δ₀ ∖ φ) · ψ · ψ) ++ Δ₁ # d
        ind′ rewrite sym eql = ind

        -- deep contraction
        ind′′ : Γ₀ ++ Γ₁ ∖ φ ⊢ ((Δ₀ ∖ φ) · ψ) ++ Δ₁ # d
        ind′′ = contraction-right-deep {Γ₀ ++ Γ₁ ∖ φ} {Δ₀ ∖ φ} {ψ} {Δ₁} ind′

        eql′ : Γ₀ ++ Γ₁ ∖ φ ⊢ ((Δ₀ ∖ φ) · ψ) ++ Δ₁ # d ≡
               Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d
        eql′ rewrite remove-≢-∷ Δ₀ φ≢ψ = refl

        goal′ : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d
        goal′ rewrite sym eql′ = ind′′
```

mix' : Γ₀ ⊢ Δ₀ # d →
      Γ₁ ⊢ Δ₁ # d →
      φ ∈ Δ₀ →
      φ ∈ Γ₁ →
      size φ ≡ 1 + d →
      -----------------------------------------
      Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d

```
mix' {¬ ψ ∷ Γ₀} {Δ₀} {d} {Γ₁} {Δ₁} {φ} (¬-left δ₀) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = goal where

    φ∈Δ₀·ψ : φ ∈ Δ₀ · ψ
    φ∈Δ₀·ψ = there φ∈Δ₀

    ind : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d
    ind = mix' δ₀ δ₁ φ∈Δ₀·ψ φ∈Γ₁ sφ

    goal : ¬ ψ ∷ Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
    goal with φ ≡? ψ
    ... | yes refl = goal′ where

        eql : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d ≡
              Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
        eql rewrite remove-∷ φ Δ₀ = refl

        ind′ : Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
        ind′ rewrite sym eql = ind

        -- in this case it suffices to weaken the l.h.s. by adding ¬ φ
        goal′ : ¬ φ ∷ Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
        goal′ = weakening-left ind′

    ... | no φ≢ψ = goal′ where

        eql : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ · ψ) ∖ φ ++ Δ₁ # d ≡
              Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ ∖ φ) · ψ ++ Δ₁ # d
        eql rewrite remove-≢-∷ Δ₀ φ≢ψ = refl

        ind′ : Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ₀ ∖ φ) · ψ ++ Δ₁ # d
        ind′ rewrite sym eql = ind

        -- we need a deep version of ¬-left
        goal′ : ¬ ψ ∷ Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
        goal′ = ¬-left-deep {Γ₀ ++ Γ₁ ∖ φ} {Δ₀ ∖ φ} {ψ} {Δ₁} ind′
```

```
mix' {Γ₀} {¬ ψ ∷ Δ₀} {d} {Γ₁} {Δ₁} {φ} (¬-right δ₀) δ₁ φ∈Δ₀·¬ψ φ∈Γ₁ sφ = {! goal  !} where

    ind : φ ∈ Δ₀ →
          ψ ∷ Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
    ind φ∈Δ₀ = mix' δ₀ δ₁ φ∈Δ₀ φ∈Γ₁ sφ

    goal : Γ₀ ++ Γ₁ ∖ φ ⊢ (¬ ψ ∷ Δ₀) ∖ φ ++ Δ₁ # d
    goal with φ ≡? ¬ ψ
    ... | yes refl = goal′ where

        eql : Γ₀ ++ Γ₁ ∖ φ ⊢ (φ ∷ Δ₀) ∖ φ ++ Δ₁ # d ≡
              Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
        eql rewrite remove-∷ φ Δ₀ = refl

        have : Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
        have with φ ∈? Δ₀
        ... | yes φ∈Δ₀ = have′′ where

            ind′ : ψ ∷ Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
            ind′ = ind φ∈Δ₀

            have′ : Γ₀ ++ Γ₁ ∖ φ ⊢ φ ∷ Δ₀ ∖ φ ++ Δ₁ # d
            have′ = ¬-right ind′

            eql′ : Γ₀ ++ Γ₁ ∖ φ ⊢ φ ∷ (Δ₀ ∖ φ) ++ Δ₁ # d ≡
                   Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
            eql′ rewrite eql = {!   !}

            have′′ : Γ₀ ++ Γ₁ ∖ φ ⊢ Δ₀ ∖ φ ++ Δ₁ # d
            have′′ rewrite sym eql′ = have′ 

        ... | no ~φ∈Δ₀ = {!   !}
        
        goal′ : Γ₀ ++ Γ₁ ∖ φ ⊢ (φ ∷ Δ₀) ∖ φ ++ Δ₁ # d
        goal′ rewrite eql = have
              
    ... | no φ≢¬ψ = {!   !}

```

```
mix' (∧-left δ₀) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
mix' (∧-right δ₀ δ₂) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
mix' (∨-left δ₀ δ₂) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
mix' (∨-right δ₀) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
```

-- * By assumption we have a derivation `d₀₀ : Γ₀ ⊢ Δ · ψ` and a derivation `d₀₁ : Γ₀ · ξ ⊢ Ξ`,
-- and a derivation `d₁ : Γ₁ ⊢ Δ₁`.

-- mix {(ψ ⇒ ξ) ∷ Γ₀} {.(_ ++ _)} {Γ₁} {Δ₁} {φ} d (⇒-left {Δ = Δ} {Ξ = Ξ} d₀₀ d₀₁) d₁ φ∈Δ₀ φ∈Γ₁ d₀≤d d₁≤d = goal where

--     d₀₀≤d : degree d₀₀ ≤ d
--     d₀₀≤d = max-≤-left d₀≤d

--     d₀₁≤d : degree d₀₁ ≤ d
--     d₀₁≤d = max-≤-right d₀≤d

--     goal : Σ (ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ ∖ φ ++ Ξ) ++ Δ₁) (λ d₂ → degree d₂ ≤ d)
--     goal with φ ≡? ψ
--     ... | yes φ≡ψ rewrite φ≡ψ = goal₀ where

--         φ∈Δ·ψ : φ ∈ Δ · ψ
--         φ∈Δ·ψ rewrite φ≡ψ = here

--         ind : Σ (Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ · ψ) ++ Δ₁) λ d₂ → degree d₂ ≤ d
--         ind = mix d d₀₀ d₁ here φ∈Γ₁ d₀₀≤d d₁≤d

--         goal₀ : Σ (ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ ++ Ξ) ++ Δ₁) (λ d₂ → degree d₂ ≤ d)
--         goal₀ with ind
--         ... | d′ , d′≤d = d′′ ,  d′′≤d where

--             d′′ : ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ ++ Ξ) ++ Δ₁
--             d′′ =
--                 BEGIN
--                     have Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ · ψ) ++ Δ₁                     by d′
--                     have ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ · ψ) ++ Δ₁             apply weakening-left at here
--                     have ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ Δ ∖ ψ ++ Δ₁                   apply tr1 at here
--                     have Δ ∖ ψ ++ Δ₁ ⊑ (Δ ∖ ψ ++ Ξ) ∖ ψ ++ Δ₁            by {!   !}
--                     have ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ ++ Ξ) ∖ ψ ++ Δ₁   apply weakening-right-⊑ at back 1 , here
--                     have ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ ++ Ξ) ++ Δ₁            apply tr2 at here
--                 END where

--                 eq1 : (Δ ∖ ψ · ψ) ≡ Δ ∖ ψ
--                 eq1 = remove-∷ ψ Δ

--                 tr1 : ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ · ψ) ++ Δ₁ → ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ Δ ∖ ψ ++ Δ₁
--                 tr1 x rewrite eq1 = x

--                 eq2 : Δ ∖ ψ ++ Ξ ∖ ψ ≡ (Δ ∖ ψ ++ Ξ)
--                 eq2 = sym (remove-++ ψ Δ Ξ)

--                 tr2 : ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ ++ Ξ) ∖ ψ ++ Δ₁ → ψ ⇒ ξ ∷ Γ₀ ++ Γ₁ ∖ ψ ⊢ (Δ ∖ ψ ++ Ξ) ++ Δ₁
--                 tr2 x rewrite eq2 = x

--             d′′≤d : degree d′′ ≤ d
--             d′′≤d = {!   !}

--     ... | no φ≢ψ with φ ∈? Δ | φ ∈? Ξ
--     ... | yes φ∈Δ | yes φ∈Ξ = d′′ , d′′≤d where

--         ind₀ : Σ (Γ₀ ++ Γ₁ ∖ φ ⊢ (ψ ∖ φ ∷ Δ) ++ Δ₁) (λ d₂ → degree d₂ ≤ d)
--         ind₀ = mix d d₀₀ d₁ (there φ∈Δ) φ∈Γ₁ d₀₀≤d d₁≤d

--         ind₁ : Σ (ξ ∷ Γ₀ ++ Γ₁ ∖ φ ⊢ Ξ ∖ φ ++ Δ₁) (λ d₂ → degree d₂ ≤ d)
--         ind₁ = mix d d₀₁ d₁ φ∈Ξ φ∈Γ₁ d₀₁≤d d₁≤d

--         tr1 : Γ₀ ++ Γ₁ ∖ φ ⊢ (ψ ∖ φ ∷ Δ) ++ Δ₁ → Γ₀ ++ Γ₁ ∖ φ ⊢ ψ ∷ Δ ∖ φ ++ Δ₁
--         tr1 x rewrite remove-≢-∷ Δ φ≢ψ = x

--         tr2'' : {{(Γ₀ ++ Γ₁) ∖ φ · ψ ⇒ ξ ⊢ (Δ ∖ φ ++ Δ₁) ++ Ξ ∖ φ ++ Δ₁}} →
--                  (Γ₀ ++ Γ₁) ∖ φ · ψ ⇒ ξ ⊢ (Δ ∖ φ ++ Ξ) ∖ φ ++ Δ₁
--         tr2'' {{x}} =
--             let instance
--                     eql : (Δ ∖ φ ++ Δ₁) ++ Ξ ∖ φ ++ Δ₁ ≡ (Δ ∖ φ ++ Ξ) ∖ φ ++ Δ₁
--                     eql = {!   !}

--             in {!   !}


--         tr2' : {{(Γ₀ ++ Γ₁) ∖ φ · ψ ⇒ ξ ⊢ (Δ ∖ φ ++ Δ₁) ++ Ξ ∖ φ ++ Δ₁}} →
--                (Γ₀ ++ Γ₁) ∖ φ · ψ ⇒ ξ ⊢ (Δ ∖ φ ++ Ξ) ++ Δ₁
--         tr2' {{x}}
--             rewrite remove-++ φ Δ Ξ = {!   !}
-- --                    assoc-++ (Δ) ∖ φ Δ₁ (Ξ ∖ φ ++ Δ₁) = {!   !}

--         tr2 : (Γ₀ ++ Γ₁) ∖ φ · ψ ⇒ ξ ⊢ (Δ ∖ φ ++ Δ₁) ++ Ξ ∖ φ ++ Δ₁ →
--               (Γ₀ ++ Γ₁) ∖ φ · ψ ⇒ ξ ⊢ (Δ ∖ φ ++ Ξ) ++ Δ₁
--         tr2 x = tr2' {{x}}
                
--         d′′ =
--             BEGIN
--             have Γ₀ ++ Γ₁ ∖ φ ⊢ (ψ ∖ φ ∷ Δ) ++ Δ₁             by dfst ind₀
--             have Γ₀ ++ Γ₁ ∖ φ ⊢ (Δ ∖ φ ++ Δ₁) · ψ             apply tr1 at here
--             have (Γ₀ ++ Γ₁) ∖ φ · ξ ⊢ Ξ ∖ φ ++ Δ₁             by dfst ind₁
--             have (Γ₀ ++ Γ₁) ∖ φ · ψ ⇒ ξ ⊢ (Δ ∖ φ ++ Δ₁) ++ Ξ ∖ φ ++ Δ₁
--                 apply ⇒-left at back 1 , here

--             have (Γ₀ ++ Γ₁) ∖ φ · ψ ⇒ ξ ⊢ (Δ ∖ φ ++ Ξ) ++ Δ₁  apply tr2 at here 
--             END where

--         d′′≤d : degree d′′ ≤ d
--         d′′≤d = {!   !}


```
mix' (⇒-left δ₀ δ₂) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
```

```
mix' (⇒-right δ₀) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
mix' (⇔-left δ₀ δ₂) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
mix' (⇔-right δ₀ δ₂) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
mix' (cut δ₀ δ₂ x) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}
mix' (degree-up δ₀ x) δ₁ φ∈Δ₀ φ∈Γ₁ sφ = {!   !}

cut-elimination : Γ ⊢ Δ # 1 + d → Γ ⊢ Δ # d
cut-elimination (weakening-left δ) = weakening-left (cut-elimination δ)
cut-elimination (weakening-right δ) = weakening-right (cut-elimination δ)
cut-elimination (exchange-left Γ δ) = exchange-left Γ (cut-elimination δ)
cut-elimination (exchange-right {Δ} Γ δ) = exchange-right {Δ} Γ (cut-elimination δ)
cut-elimination (contraction-left δ) = contraction-left (cut-elimination δ)
cut-elimination (contraction-right δ) = contraction-right (cut-elimination δ)
cut-elimination (¬-left δ) = ¬-left (cut-elimination δ)
cut-elimination (¬-right δ) = ¬-right (cut-elimination δ)
cut-elimination (∧-left δ) = ∧-left (cut-elimination δ)
cut-elimination (∧-right δ₀ δ₁) = ∧-right (cut-elimination δ₀) (cut-elimination δ₁)
cut-elimination (∨-left δ₀ δ₁) = ∨-left (cut-elimination δ₀) (cut-elimination δ₁)
cut-elimination (∨-right δ₀) = ∨-right (cut-elimination δ₀)
cut-elimination (⇒-left δ₀ δ₁) = ⇒-left (cut-elimination δ₀) (cut-elimination δ₁)
cut-elimination (⇒-right δ) = ⇒-right (cut-elimination δ)
cut-elimination (⇔-left δ₀ δ₁) = ⇔-left (cut-elimination δ₀) (cut-elimination δ₁)
cut-elimination (⇔-right δ₀ δ₁) = ⇔-right (cut-elimination δ₀) (cut-elimination δ₁)

cut-elimination (cut {Γ} {Δ} {φ} {suc d} {Ξ} δ₀ δ₁ φ≤1+d)
    with cut-elimination δ₀ |
         cut-elimination δ₁
... | δ₀′ | δ₁′
    with size φ ≤? d
... | yes φ≤d = cut δ₀′ δ₁′ φ≤d
... | no ~φ≤d
    with m≤1+n→~m≤n→m≡1+n φ≤1+d ~φ≤d
... | φ≡1+d =
    BEGIN
    have Γ ++ Γ ∖ φ ⊢ Δ ∖ φ ++ Ξ # d  by mix δ₀′ δ₁′ φ≡1+d -- mix lemma!
    have Γ ∖ φ ⊑ Γ                         by remove-⊑ φ Γ
    have Γ ⊢ Δ ∖ φ ++ Ξ # d                apply contraction-left#-⊑ at back 1 , here
    have Δ ∖ φ ⊑ Δ                         by remove-⊑ φ Δ
    have Δ ∖ φ ++ Ξ ⊑ Δ ++ Ξ               apply ++-⊑-right Ξ at here
    have Γ ⊢ Δ ++ Ξ # d                         apply weakening-right#-⊑ at back 2 , here
    END

cut-elimination (degree-up {Γ} {Δ} {φ} {d₀} {suc d₁} δ d₀≤1+d₁)
    with d₀ ≡? 1 + d₁
... | yes d₀≡1+d₁ rewrite d₀≡1+d₁ = cut-elimination δ
... | no d₀≢1+d₁
    with m≤1+n→~m≡1+n→m≤n d₀≤1+d₁ d₀≢1+d₁
... | d₀≤d₁ = degree-up δ d₀≤d₁

```




