---
title: "Hilbert-style proof system for propositional logic 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-} -- --rewriting --confluence-check
open import part0.index

module part1.Hilbert (n′ : ℕ) where
open import part1.CharacteristicFormulas n′ public hiding (ϱtt; ϱff; LEM)

private
  variable
    φ ψ θ ξ : Formula
    Γ Δ : Context
```

References:

* Proof pearl @CaiKaposiAltenkirch:2015 for propositional logic.
* modal logic S5 @Bentzen:arXiv:2019.

# Hilbert-style proof system

We present a Hilbert-style proof system to establish tautologies of propositional logic.
The proof system consists of several *axioms* and a single *inference rule*.

```
infixr 5 _⊢_
infix 12 Ass_
data _⊢_ : Context → Formula → Set where

  -- assumption
  Ass_ : φ ∈ Γ →
        -----
        Γ ⊢ φ

  -- axioms for implication and ⊥
  A1 : Γ ⊢ φ ⇒ ψ ⇒ φ
  A2 : Γ ⊢ (φ ⇒ ψ ⇒ θ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ θ 
  A3 : Γ ⊢ ((φ ⇒ ⊥) ⇒ ⊥) ⇒ φ

  -- axiom for true
  T1 : Γ ⊢ ⊤

  -- axioms for negation
  N1 : Γ ⊢ ¬ φ ⇒ φ ⇒ ⊥
  N2 : Γ ⊢ (φ ⇒ ⊥) ⇒ ¬ φ 

  -- axioms for disjunction
  D1 : Γ ⊢ φ ⇒ φ ∨ ψ
  D2 : Γ ⊢ ψ ⇒ φ ∨ ψ
  D3 : Γ ⊢ (φ ⇒ θ) ⇒ (ψ ⇒ θ) ⇒ (φ ∨ ψ) ⇒ θ

  -- axioms for conjunction
  C1 : Γ ⊢ φ ∧ ψ ⇒ φ
  C2 : Γ ⊢ φ ∧ ψ ⇒ ψ
  C3 : Γ ⊢ φ ⇒ ψ ⇒ φ ∧ ψ

  -- axioms for bi-implication
  E1 : Γ ⊢ (φ ⇔ ψ) ⇒ φ ⇒ ψ
  E2 : Γ ⊢ (φ ⇔ ψ) ⇒ ψ ⇒ φ
  E3 : Γ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ (φ ⇔ ψ)

  -- modus ponens
  MP : Γ ⊢ φ ⇒ ψ →
       Γ ⊢ φ →
       -----
       Γ ⊢ ψ
```

We write `Γ ⊢ φ` when there is *proof* of `φ` (the *goal* of the proof) from the assumptions in `Γ` (the *context* of the proof).
The axioms can be broken down into 7 groups:

1) The first group consists of a single axiom !ref(_⊢_)(Ass),
which says that we can prove `φ` provided it is an assumption in `Γ.

2) The second group of axioms !ref(_⊢_)(A1), !ref(_⊢_)(A2), and !ref(_⊢_)(A3) models the implication connective !remoteRef(part1)(Formula)(_⇒_) and !remoteRef(part1)(Formula)(⊥).
In particular, !ref(_⊢_)(A3) embodies the law of *double negation elimination* (DNE) and makes the proof system "classical" (as opposed to intuitionistic).

3) The third group consists of a single axiom !ref(_⊢_)(T1) modeling !remoteRef(part1)(Formula)(⊤).

4) The fourth group of axioms !ref(_⊢_)(N1) and !ref(_⊢_)(N2) models negation !remoteRef(part1)(Formula)(¬_) in terms of implication !remoteRef(part1)(Formula)(_⇒_) and false !remoteRef(part1)(Formula)(⊥).

5) The fifth group consists of three axioms !ref(_⊢_)(D1), !ref(_⊢_)(D2), and !ref(_⊢_)(D3) modelling disjunction !remoteRef(part1)(Formula)(_∨_).

6) The sixth group consists of three axioms !ref(_⊢_)(C1), !ref(_⊢_)(C2), and !ref(_⊢_)(C3) modelling conjunction !remoteRef(part1)(Formula)(_∧_).

7) The seventh and last group consists of three axioms !ref(_⊢_)(E1), !ref(_⊢_)(E2), and !ref(_⊢_)(E3) modelling bi-implication !remoteRef(part1)(Formula)(_⇔_).

Finally, we have the *modus ponens* inference rule !ref(_⊢_)(MP) which allows us to derive new theorems from previous ones.
In order get familiar with writing proofs `Γ ⊢ φ`,
we begin with the proof of the simplest theorem of all:

```
refl-⇒ : Γ ⊢ φ ⇒ φ
refl-⇒ {Γ} {φ} = S5 where

  S1 : Γ ⊢ φ ⇒ φ ⇒ φ
  S1 = A1

  S2 : Γ ⊢ φ ⇒ (φ ⇒ φ) ⇒ φ
  S2 = A1

  S3 : Γ ⊢ (φ ⇒ (φ ⇒ φ) ⇒ φ) ⇒ (φ ⇒ φ ⇒ φ) ⇒ φ ⇒ φ
  S3 = A2

  S4 : Γ ⊢ (φ ⇒ φ ⇒ φ) ⇒ φ ⇒ φ
  S4 = MP S3 S2

  S5 : Γ ⊢ φ ⇒ φ
  S5 = MP S4 S1
```

Writing explicit proofs in this style is a particularly tedious activity,
some of which is unavoidable.
In order to make our life easier, we will prove some metatheorems (i.e., theorems about theorems)
such as the monotonicity and deduction theorems,
which will allow us to write proofs more concisely.

## Monotonicity

The proof system !ref(_⊢_) is *monotonic* in the sense that adding additional assumptions can only enlarge the set of formulas it can prove.
This is a fundamental property of so-called "monotone logics", whereby adding new knowledge can only increase our knowledge of the world.
(On the contrary, in "non-monotone logics" adding new knowledge can invalidate previous knowledge, which may need to be retracted.)

!theorem(#theorem:monotonicity)(Monotonicity)
~~~
For every context `Γ` and formulas `φ`, `ψ`:

```
mon-⊢ : Γ ⊢ φ →
        ---------
        Γ · ψ ⊢ φ
```
~~~

!hide
~~~
The proof goes by a monotone (pun intended) structural induction.
~~~
~~~
```
mon-⊢ (Ass φ∈Δ) = Ass there φ∈Δ

mon-⊢ T1 = T1

mon-⊢ N1 = N1
mon-⊢ N2 = N2

mon-⊢ A1 = A1
mon-⊢ A2 = A2
mon-⊢ A3 = A3

mon-⊢ D1 = D1
mon-⊢ D2 = D2
mon-⊢ D3 = D3

mon-⊢ C1 = C1
mon-⊢ C2 = C2
mon-⊢ C3 = C3

mon-⊢ E1 = E1
mon-⊢ E2 = E2
mon-⊢ E3 = E3

mon-⊢ (MP Δ⊢φ Δ⊢ψ) = MP (mon-⊢ Δ⊢φ) (mon-⊢ Δ⊢ψ)
```
~~~

!exercise(#exercise:mon2)
~~~
The [monotonicity theorem](#theorem:monotonicity) allows us to add a single formula to the context.
Sometimes it is convenient to add *two* formulas to the context. State and prove this fact (as `mon2-⊢`).
~~~
~~~
```
mon2-⊢ : Δ ⊢ φ →
         -------------
         Δ · ψ · ξ ⊢ φ

mon2-⊢ = mon-⊢ ∘ mon-⊢
```
~~~

## Deduction theorem

Our second tool to assist us with writing proofs is the *deduction theorem*,
which allows us to move assumptions from the context back and forth.
In fact, we have already seen a semantic version !remoteRef(part1)(Semantics)(semDT1) and !remoteRef(part1)(Semantics)(semDT2) of the deduction theorem in the [first chapter](../../Semantics).
We present here the proof-theoretic incarnation of the deduction theorem.
As its semantic counterpart, it consists of two separate directions.
The first direction allows us to move an assumption from the formula to the context:

```
DT1 : Γ ⊢ φ ⇒ ψ →
      ---------
      Γ · φ ⊢ ψ

DT1 {Γ} {φ} {ψ} Γ⊢φ⇒ψ = MP Γ,φ⊢φ⇒ψ Γ,φ⊢φ where

  Γ,φ⊢φ⇒ψ : φ ∷ Γ ⊢ φ ⇒ ψ
  Γ,φ⊢φ⇒ψ = mon-⊢ {ψ = φ} Γ⊢φ⇒ψ

  Γ,φ⊢φ : φ ∷ Γ ⊢ φ
  Γ,φ⊢φ = Ass here
```

The proof is a straightforward application of modus ponens !ref(_⊢_)(MP) and monotonicity !ref(mon-⊢).
The second direction of the deduction theorem allows us to move a formula from the context to the goal:

```
DT2 : Γ · φ ⊢ ψ →
      ---------
      Γ ⊢ φ ⇒ ψ
```

This is the most useful direction of the deduction theorem.
The proof of !ref(DT2) is more elaborated,
as an immediate confirmation that it is really doing some work for us.
It goes by structural induction on proofs:

```
DT2 (Ass here) = refl-⇒

DT2 (Ass (there ψ∈Γ)) = MP A1 (Ass ψ∈Γ)

DT2 A1 = MP A1 A1
DT2 A2 = MP A1 A2
DT2 A3 = MP A1 A3

DT2 T1 = MP A1 T1

DT2 N1 = MP A1 N1
DT2 N2 = MP A1 N2

DT2 D1 = MP A1 D1
DT2 D2 = MP A1 D2
DT2 D3 = MP A1 D3

DT2 C1 = MP A1 C1
DT2 C2 = MP A1 C2
DT2 C3 = MP A1 C3

DT2 E1 = MP A1 E1
DT2 E2 = MP A1 E2
DT2 E3 = MP A1 E3

DT2 {Γ} {φ} {ψ} (MP {φ = ξ} φ,Γ⊢ξ⇒ψ φ,Γ⊢ξ) = SS where

  S1 : Γ ⊢ φ ⇒ ξ
  S1 = DT2 φ,Γ⊢ξ

  S2 : Γ ⊢ φ ⇒ ξ ⇒ ψ
  S2 = DT2 φ,Γ⊢ξ⇒ψ

  S3 : Γ ⊢ (φ ⇒ ξ) ⇒ φ ⇒ ψ
  S3 = MP A2 S2

  SS : Γ ⊢ φ ⇒ ψ
  SS = MP S3 S1
```

!example(#example:refl)
~~~
Testifying to the usefulness of !ref(DT2), we can reprove !ref(refl-⇒) with a one-liner:

```
refl-⇒' : Γ ⊢ φ ⇒ φ
refl-⇒' = DT2 (Ass here) 
```
~~~

Putting together the two halves of the deduction theorem,
we obtain the following theorem.

!theorem(#theorem:DT)(Deduction theorem)
~~~
For every context `Γ` and formulas `φ`, `ψ`, we have:
```
DT : Γ ⊢ φ ⇒ ψ ↔ Γ · φ ⊢ ψ
DT = DT1 , DT2
```
~~~

!exercise(#exercise:deduction)
~~~
It is sometimes useful to apply the deduction theorem to "long implications" of the form
`Γ Imply φ ≡ φ₁ ⇒ ... ⇒ φₙ ⇒ φ`, with `Γ` a sequence of formulas of the form `∅ · φₙ · ... · φ₁`
(c.f. !remoteRef(part1)(Semantics)(Imply)).
Prove the following generalisation of the deduction theorem to long implications:

```
longDT : ε ⊢ Γ Imply φ →
         -----
         Γ ⊢ φ
```
~~~
~~~
```
longDT {ε} ε⊢ΓImplyφ = ε⊢ΓImplyφ
longDT {ψ ∷ Γ} {φ} ε⊢ΓImply[ψ⇒φ]
  with longDT {Γ} {ψ ⇒ φ} ε⊢ΓImply[ψ⇒φ]
... | ind = DT1 ind
```
~~~

TODO: Introduce the !ref(part0)(TList)(TList) syntax.

!exercise(#exercise:B1-B4)
~~~
Prove the following theorems:

```
B1 : Γ ⊢ ⊥ ⇒ φ
B2 : Γ ⊢ (φ ⇒ ⊥) ⇒ φ ⇒ ψ
B3 : Γ ⊢ (φ ⇒ ψ) ⇒ ((φ ⇒ ⊥) ⇒ ψ) ⇒ ψ
B4 : Γ ⊢ φ ⇒ (ψ ⇒ ⊥) ⇒ (φ ⇒ ψ) ⇒ ⊥
```

Theorem !ref(B1) is known as the *principle of explosion* ("ex falso [sequitur] quodlibet").
~~~
~~~
```
B1 {Γ} {φ} =
  BEGIN
  have Γ · ⊥ · φ ⇒ ⊥ ⊢ ⊥    by Ass back 1
  have Γ · ⊥ ⊢ (φ ⇒ ⊥) ⇒ ⊥  apply DT2 at here
  have Γ · ⊥ ⊢ φ            apply MP A3 at here
  have Γ ⊢ ⊥ ⇒ φ            apply DT2 at here
  END
```

```
B2 {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ⇒ ⊥ · φ ⊢ ⊥      by DT1 (DT1 (refl-⇒))
  have Γ · φ ⇒ ⊥ · φ ⊢ ψ      apply MP B1 at here
  have Γ ⊢ (φ ⇒ ⊥) ⇒ φ ⇒ ψ    apply DT2 ∘ DT2 at here
  END
```

```
B3 {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ · φ ⊢ φ        by Ass here
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ · φ ⊢ φ ⇒ ψ    by Ass back 3
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ · φ ⊢ ψ        apply MP at here , back 1
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ · φ ⊢ ψ ⇒ ⊥    by Ass back 1
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ · φ ⊢ ⊥        apply MP at here , back 1
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ ⊢ φ ⇒ ⊥        apply DT2 at here
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ ⊢ (φ ⇒ ⊥) ⇒ ψ  by Ass back 1
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ ⊢ ψ            apply MP at here , back 1
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ ⊢ ψ ⇒ ⊥        by Ass here
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ · ψ ⇒ ⊥ ⊢ ⊥            apply MP at here , back 1
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ ⊢ (ψ ⇒ ⊥) ⇒ ⊥          apply DT2 at here
  have Γ · φ ⇒ ψ · (φ ⇒ ⊥) ⇒ ψ ⊢ ψ                    apply MP A3 at here
  have Γ ⊢ (φ ⇒ ψ) ⇒ ((φ ⇒ ⊥) ⇒ ψ) ⇒ ψ                apply DT2 ∘ DT2 at here
  END
```

```
B4 {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ · ψ ⇒ ⊥ · φ ⇒ ψ ⊢ φ        by Ass back 2
  have Γ · φ · ψ ⇒ ⊥ · φ ⇒ ψ ⊢ φ ⇒ ψ    by Ass here
  have Γ · φ · ψ ⇒ ⊥ · φ ⇒ ψ ⊢ ψ        apply MP at here , back 1
  have Γ · φ · ψ ⇒ ⊥ · φ ⇒ ψ ⊢ ψ ⇒ ⊥    by Ass back 1
  have Γ · φ · ψ ⇒ ⊥ · φ ⇒ ψ ⊢ ⊥        apply MP at here , back 1
  have Γ ⊢ φ ⇒ (ψ ⇒ ⊥) ⇒ (φ ⇒ ψ) ⇒ ⊥    apply DT2 ∘ DT2 ∘ DT2 at here
  END
```
~~~

## Soundness

!hide
~~~
A proof system is *sound* if it can only prove logical consequences of the context.
It is an easy, but important sanity check to verify that our proof rules are sound:

```
soundness :
  Δ ⊢ φ →
  -----
  Δ ⊨ φ
```

The proof goes by structural induction on proofs using the method of truth tables.
~~~
~~~
```
soundness (Ass ψ∈Δ) ϱ ⟦Δ⟧ = ⟦Δ⟧ ψ∈Δ

soundness {φ = ⊤} T1 ϱ _ = refl

soundness {φ = ¬ φ ⇒ φ ⇒ ⊥} N1 ϱ _
  with ⟦ φ ⟧ ϱ
... | tt = refl
... | ff = refl

soundness {φ = (φ ⇒ ⊥) ⇒ ¬ φ} N2 ϱ _
  with ⟦ φ ⟧ ϱ
... | tt = refl
... | ff = refl

soundness {φ = φ ⇒ ψ ⇒ φ} A1 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = (φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ ξ} A2 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ ξ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = ((φ ⇒ ⊥) ⇒ ⊥) ⇒ φ} A3 ϱ _
  with ⟦ φ ⟧ ϱ
... | tt = refl
... | ff = refl

soundness {φ = φ ⇒ ψ ∨ ξ} D1 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ ξ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = φ ⇒ ψ ∨ ξ} D2 ϱ _ 
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ ξ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = (φ ⇒ θ) ⇒ (ψ ⇒ θ) ⇒ (φ ∨ ψ) ⇒ θ} D3 ϱ _ 
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ θ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = φ ∧ ψ ⇒ φ} C1 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = φ ∧ ψ ⇒ ψ} C2 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = φ ⇒ ψ ⇒ φ ∧ ψ} C3 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = (φ ⇔ ψ) ⇒ φ ⇒ ψ} E1 ϱ _ 
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = (φ ⇔ ψ) ⇒ ψ ⇒ φ} E2 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = (φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ (φ ⇔ ψ)} E3 ϱ _ 
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

-- strong soundness of modus ponens
soundness {φ = ψ} (MP {φ = φ} Δ⊢φ⇒ψ Δ⊢φ) ϱ ⟦Δ⟧
  with soundness Δ⊢φ⇒ψ ϱ ⟦Δ⟧ |
       soundness Δ⊢φ ϱ ⟦Δ⟧
... | ⟦φ⇒ψ⟧ϱ≡tt | ⟦φ⟧ϱ≡tt
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
```
~~~

# Completeness for the `{⇒, ⊥}` fragment {#completeness-fragment}

Soundness is only half of the story regarding a proof system, and the easier half for that matter.
The second half of the story is that of completeness:
A proof system is *complete* if it can prove any logical consequence of the context.
In this section we will prove that Hilbert-style proof system is complete in the restricted case of formulas in the `{⇒, ⊥}` fragment:

```
completeness1 :
    Formula[⇒,⊥] φ →
    All Formula[⇒,⊥] Γ →
    Γ ⊨ φ →
    -----
    Γ ⊢ φ
```

This will be used as a stepping stone for the proof of completeness for the [full fragment](#completeness).
In fact, it suffices (and its easier) to prove the completeness theorem in the special case of an empty context.
This is called the *weak completeness* theorem:

```
weak-completeness1 :
  Formula[⇒,⊥] φ →
  ε ⊨ φ →
  -----
  ε ⊢ φ
```

The central idea behind the proof of the (weak) completeness theorem is to have the proof system simulate the method of truth tables.

```
infix 51 _^_ _^^_

_^_ : Formula → Val → Formula
φ ^ ϱ = Cond𝔹 φ (φ ⇒ ⊥) (⟦ φ ⟧ ϱ)

_^^_ : Context → Val → Context
φs ^^ ϱ = map (λ φ → φ ^ ϱ) φs

-- list of all variables
vars : Context
vars = map `_ propNames
```

## Core lemma 1

```
core-lemma : ∀ φ (_ : Formula[⇒,⊥] φ) (ϱ : Val) →
  ------------------
  vars ^^ ϱ  ⊢ φ ^ ϱ
  
core-lemma .⊥ ⊥ ϱ = refl-⇒
core-lemma .(` p) (` p) ϱ = Ass p^ϱ∈ass where

  p∈ps : p ∈ propNames
  p∈ps = findPropName p

  `p∈vars : ` p ∈ vars
  `p∈vars =  map-∈ `_ {enumFin _} p∈ps

  p^ϱ∈ass : ` p ^ ϱ ∈ (vars ^^ ϱ)
  p^ϱ∈ass = map-∈ (λ x → x ^ ϱ) {vars} `p∈vars

core-lemma (φ ⇒ ψ) (viewφ ⇒ viewψ) ϱ
  with core-lemma ψ viewψ ϱ | inspect (⟦ ψ ⟧ ϱ)
... | indψ | it tt ⟦ψ⟧ϱ≡tt
  rewrite ⟦ψ⟧ϱ≡tt |
          ⇒𝔹-rewrite-tt-right (⟦ φ ⟧ ϱ) = MP A1 indψ 
... | indψ | it ff ⟦ψ⟧ϱ≡ff rewrite ⟦ψ⟧ϱ≡ff
  with core-lemma φ viewφ ϱ | inspect (⟦ φ ⟧ ϱ)
... | indφ | it tt ⟦φ⟧ϱ≡tt rewrite ⟦φ⟧ϱ≡tt = MP (MP B4 indφ) indψ
... | indφ | it ff ⟦φ⟧ϱ≡ff rewrite ⟦φ⟧ϱ≡ff = MP B2 indφ
```

## Core lemma 2

```
core-lemma2 :
  Formula[⇒,⊥] φ →
  ε ⊨ φ →
  ∀ m ϱ →
  m ≤ n →
  --------------------
  drop m vars ^^ ϱ ⊢ φ

core-lemma2 {φ} viewφ ⊨φ 0 ϱ _ = repl fromCoreLemma (cong (λ C → vars ^^ ϱ ⊢ C) φ^ϱ≡φ) where

  fromCoreLemma : vars ^^ ϱ ⊢ φ ^ ϱ
  fromCoreLemma = core-lemma φ viewφ ϱ

  ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
  ⟦φ⟧ϱ≡tt = ⊨φ ϱ λ ()
  
  φ^ϱ≡φ : φ ^ ϱ ≡ φ
  φ^ϱ≡φ rewrite ⟦φ⟧ϱ≡tt = refl

core-lemma2 {φ} viewφ ⊨φ (suc m) ϱ sucm≤sucn
  with core-lemma2 {φ} viewφ ⊨φ m
... | ind = goal where

  distinct-ps : distinct propNames
  distinct-ps = enumFinDistinct _

  eql : length propNames ≡ n
  eql = enumFinLen n

  lenps>m : length propNames > m
  lenps>m rewrite eql = sucm≤sucn
                       
  v : PropName
  v = get-ne m propNames lenps>m

  v∈ps : v ∈ propNames ! m
  v∈ps = get-ne-∈! _ _ _
  
  ϱtt ϱff : Val
  ϱtt = ϱ [ v ↦ tt ]
  ϱff = ϱ [ v ↦ ff ]

  indtt : drop m vars ^^ ϱtt ⊢ φ
  indtt = ind ϱtt (trans-≤ n≤sucn sucm≤sucn)

  indff : drop m vars ^^ ϱff ⊢ φ
  indff = ind ϱff (trans-≤ n≤sucn sucm≤sucn)

  ϱttv≡tt : ϱtt v ≡ tt
  ϱttv≡tt = update-≡ v

  v^ϱtt≡v : ` v ^ ϱtt ≡ ` v
  v^ϱtt≡v rewrite ϱttv≡tt = refl

  ϱffv≡ff : ϱff v ≡ ff
  ϱffv≡ff = update-≡ v

  v^ϱff≡¬v : ` v ^ ϱff ≡ ` v ⇒ ⊥
  v^ϱff≡¬v rewrite ϱffv≡ff = refl

  drops : drop m propNames ≡ v ∷ drop (suc m) propNames
  drops = drop-cons m propNames lenps>m

  agree : ∀ b → map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agree b = map-Agree _ _ _ agree2 where

    agree2 : Agree (λ p → ` p ^ (ϱ [ v ↦ b ])) (λ p → ` p ^ ϱ) (drop (suc m) propNames)
    agree2 = Agree2-∘ (λ p → Cond𝔹 (` p) (` p ⇒ ⊥)) (ϱ [ v ↦ b ]) ϱ (drop (suc m) propNames) agree1 where

     agree1 : Agree (ϱ [ v ↦ b ]) ϱ (drop (suc m) propNames)
     agree1 {p} p∈dropps = update-≢ v≢p where

       have : ∃[ k ] p ∈ drop (suc m) propNames ! k
       have = ∈→∈! _ _ p∈dropps

       k : ℕ
       k = dfst have

       p∈dropps!k : p ∈ drop (suc m) propNames ! k
       p∈dropps!k = dsnd have

       p∈ps : p ∈ propNames ! (suc m + k)
       p∈ps = drop-∈! p (suc m) _ _ p∈dropps!k

       v≢p : v ≢ p
       v≢p with v ≡? p
       ... | no proof = proof

       -- derive a contradiction
       ... | yes refl with distinct-ps m (suc m + k) v v∈ps p∈ps
       ... | impossible = F-elim (diseq impossible) where

         ineq : m < suc (m + k)
         ineq =  begin<
           m <≤⟨ n<sucn ⟩
           suc m
             ≤⟨ cong-≤ (Suc □) m≤m+k ⟩
           suc (m + k)
           ∎≤ where

             m≤m+k : m ≤ m + k
             m≤m+k = ≤+

         diseq : m ≢ suc (m + k)
         diseq = <→≢ ineq

  agreett : map (λ p → ` p ^ ϱtt) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agreett = agree tt

  agreeff : map (λ p → ` p ^ ϱff) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agreeff = agree ff

  equality : ∀ b → drop m vars ^^ (ϱ [ v ↦ b ]) ≡ Cond𝔹 (` v) (` v ⇒ ⊥) b ∷ drop (suc m) vars ^^ ϱ
  equality b = begin
    drop m vars ^^ (ϱ [ v ↦ b ])
      ≡⟨ cong (λ C → C ^^ (ϱ [ v ↦ b ])) (drop-map _ m propNames) ⟩
    map `_ (drop m propNames) ^^ (ϱ [ v ↦ b ])
      ≡⟨ map-∘ _ _ (drop m propNames) ⟩
    map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop m propNames)
      ≡⟨ cong (map λ p → ` p ^ (ϱ [ v ↦ b ])) drops ⟩
    map (λ p → ` p ^ (ϱ [ v ↦ b ])) (v ∷ drop (suc m) propNames)
      ≡⟨⟩
    (` v ^ (ϱ [ v ↦ b ])) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨⟩
    Cond𝔹 (` v) (` v ⇒ ⊥) (⟦ ` v ⟧ (ϱ [ v ↦ b ])) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨⟩
    Cond𝔹 (` v) (` v ⇒ ⊥) ((ϱ [ v ↦ b ]) v) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨ cong (λ C → Cond𝔹 (` v) (` v ⇒ ⊥) C ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)) (update-≡ v)  ⟩
    ψ₀ ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨ cong (λ C → ψ₀ ∷ C) (agree b) ⟩
    ψ₀ ∷ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
      ≡⟨ cong (λ C → ψ₀ ∷ C) (sym (map-∘ _ _ (drop (suc m) propNames)))  ⟩
    ψ₀ ∷ map `_ (drop (suc m) propNames) ^^ ϱ
      ≡⟨ cong (λ C → ψ₀ ∷ C ^^ ϱ) (sym (drop-map _ (suc m) propNames)) ⟩
    ψ₀ ∷ drop (suc m) vars ^^ ϱ ∎ where

      ψ₀ : Formula
      ψ₀ = Cond𝔹 (` v) (` v ⇒ ⊥) b

  eql-tt : drop m vars ^^ ϱtt ≡ ` v ∷ drop (suc m) vars ^^ ϱ
  eql-tt = equality tt

  eql-ff : drop m vars ^^ ϱff ≡ (` v ⇒ ⊥) ∷ drop (suc m) vars ^^ ϱ
  eql-ff = equality ff

  indtt' : drop (suc m) vars ^^ ϱ · ` v ⊢ φ
  indtt' = repl indtt (cong (λ C → C ⊢ φ) eql-tt)

  indff' : drop (suc m) vars ^^ ϱ · ` v ⇒ ⊥ ⊢ φ
  indff' = repl indff (cong (λ C → C ⊢ φ) eql-ff)

  indtt'' : drop (suc m) vars ^^ ϱ ⊢ ` v ⇒ φ
  indtt'' = DT2 indtt'

  indff'' : drop (suc m) vars ^^ ϱ ⊢ (` v ⇒ ⊥) ⇒ φ
  indff'' = DT2 indff' 

  goal : drop (suc m) vars ^^ ϱ ⊢ φ
  goal = MP (MP B3 indtt'') indff''
```

## Back to completeness

```
weak-completeness1 {φ} viewφ ⊨φ = ε⊢φ where

  anyVal : Val
  anyVal = λ _ → tt

  have : drop n vars ^^ anyVal ⊢ φ
  have = core-lemma2 viewφ ⊨φ n anyVal refl-≤

  vars-len : length vars ≡ n
  vars-len = begin
     length vars ≡⟨⟩
     length {A = Formula} (map `_ (enumFin _)) ≡⟨ map-length `_ (enumFin _) ⟩
     length (enumFin _) ≡⟨ enumFinLen n ⟩
     n ∎

  eql : drop n vars ≡ ε
  eql = begin
    drop n vars ≡⟨ cong (λ C → drop C vars) (sym vars-len) ⟩
    drop (length vars) vars ≡⟨ drop-all vars ⟩
    ε ∎

  eql1 : drop n vars ^^ anyVal ≡ ε
  eql1 = begin
     drop n vars ^^ anyVal
       ≡⟨ cong (λ C → C ^^ anyVal) eql  ⟩
     ε ^^ anyVal
       ≡⟨⟩
     ε ∎
  
  ε⊢φ : ε ⊢ φ
  ε⊢φ = repl have (cong (λ C → C ⊢ φ) eql1)


completeness1 {φ} {Γ} viewφ viewΓ = begin→
  Γ ⊨ φ
    →⟨ longSemDT1 ⟩
  ε ⊨ Γ Imply φ
    →⟨ weak-completeness1 (view Γ φ viewφ viewΓ) ⟩
  ε ⊢ Γ Imply φ
    →⟨ longDT ⟩
  Γ ⊢ φ
  ∎→  where

  view : ∀ Δ φ → Formula[⇒,⊥] φ → All Formula[⇒,⊥] Δ → Formula[⇒,⊥] (Δ Imply φ)
  view ε φ viewφ viewΔ = viewφ
  view (ψ ∷ Δ) φ viewφ viewΔ = view Δ (ψ ⇒ φ) (viewψ ⇒ viewφ) (viewΔ ∘ there) where

    viewψ : Formula[⇒,⊥] ψ
    viewψ = viewΔ here
```

# Translation to the `{⇒ , ⊥}` fragment

## Equivalences

## Congruence properties

## Translation


```
contraposition : Γ ⊢ (ψ ⇒ φ) ⇒ ¬ φ ⇒ ¬ ψ
contraposition {Γ} {ψ} {φ} =
  BEGIN
  have Γ · ψ ⇒ φ · ¬ φ · ψ ⊢ ψ ⇒ φ  by Ass back 2
  have Γ · ψ ⇒ φ · ¬ φ · ψ ⊢ ψ      by Ass here
  have Γ · ψ ⇒ φ · ¬ φ · ψ ⊢ φ      apply MP at back 1 , here

  have Γ · ψ ⇒ φ · ¬ φ · ψ ⊢ ¬ φ    by Ass back 1
  have Γ · ψ ⇒ φ · ¬ φ · ψ ⊢ φ ⇒ ⊥  apply MP N1 at here
  
  have Γ · ψ ⇒ φ · ¬ φ · ψ ⊢ ⊥      apply MP at here , back 2
  have Γ · ψ ⇒ φ · ¬ φ ⊢ ψ ⇒ ⊥      apply DT2 at here
  have Γ · ψ ⇒ φ · ¬ φ ⊢ ¬ ψ        apply MP N2 at here
  have Γ · ψ ⇒ φ ⊢ ¬ φ ⇒ ¬ ψ        apply DT2 at here
  have Γ ⊢ (ψ ⇒ φ) ⇒ ¬ φ ⇒ ¬ ψ      apply DT2 at here
  END
```


```
DN1 : Γ ⊢ ¬ ¬ φ ⇒ φ
DN1 {Γ} {φ} =
  BEGIN
  have Γ · ¬ ¬ φ · φ ⇒ ⊥ ⊢ φ ⇒ ⊥      by Ass here
  have Γ · ¬ ¬ φ · φ ⇒ ⊥ ⊢ ¬ φ        apply MP N2 at here
  have Γ · ¬ ¬ φ · φ ⇒ ⊥ ⊢ ¬ ¬ φ      by Ass back 1
  have Γ · ¬ ¬ φ · φ ⇒ ⊥ ⊢ ¬ φ ⇒ ⊥    apply MP N1 at here
  have Γ · ¬ ¬ φ · φ ⇒ ⊥ ⊢ ⊥          apply MP at here , back 2
  have Γ · ¬ ¬ φ ⊢ (φ ⇒ ⊥) ⇒ ⊥        apply DT2 at here
  have Γ · ¬ ¬ φ ⊢ φ                  apply MP A3 at here
  have Γ ⊢ ¬ ¬ φ ⇒ φ                  apply DT2 at here
  END

-- DN2 : Γ ⊢ φ ⇒ ¬ ¬ φ
-- DN2 = {!   !}

irref-LEM : Γ ⊢ ¬ ¬ (φ ∨ ¬ φ)
irref-LEM {Γ} {φ} =
  BEGIN
  have Γ · ¬ (φ ∨ ¬ φ) · φ ⊢ φ              by Ass here
  have Γ · ¬ (φ ∨ ¬ φ) · φ ⊢ φ ∨ ¬ φ        apply MP D1 at here

  have Γ · ¬ (φ ∨ ¬ φ) · φ ⊢ ¬ (φ ∨ ¬ φ)    by Ass back 1
  have Γ · ¬ (φ ∨ ¬ φ) · φ ⊢ (φ ∨ ¬ φ) ⇒ ⊥  apply MP N1 at here
  have Γ · ¬ (φ ∨ ¬ φ) · φ ⊢ ⊥              apply MP at here , back 2
  have Γ · ¬ (φ ∨ ¬ φ) ⊢ φ ⇒ ⊥              apply DT2 at here
  have Γ · ¬ (φ ∨ ¬ φ) ⊢ ¬ φ                apply MP N2 at here
  have Γ · ¬ (φ ∨ ¬ φ) ⊢ φ ∨ ¬ φ            apply MP D2 at here
  have Γ · ¬ (φ ∨ ¬ φ) ⊢ ¬ (φ ∨ ¬ φ)        by Ass here
  have Γ · ¬ (φ ∨ ¬ φ) ⊢ (φ ∨ ¬ φ) ⇒ ⊥      apply MP N1 at here
  
  have Γ · ¬ (φ ∨ ¬ φ) ⊢ ⊥                  apply MP at here , back 2
  have Γ ⊢ (¬ (φ ∨ ¬ φ)) ⇒ ⊥                apply DT2 at here
  have Γ ⊢ ¬ ¬ (φ ∨ ¬ φ)                    apply MP N2 at here
  END

LEM : Γ ⊢ φ ∨ ¬ φ
LEM = MP DN1 irref-LEM
```


```
MP2 : Γ ⊢ φ ⇒ ψ ⇒ ξ →
      Γ ⊢ φ →
      Γ ⊢ ψ →
      ------
      Γ ⊢ ξ

MP2 Γ⊢φ⇒ψ⇒ξ Γ⊢φ Γ⊢ψ = MP (MP Γ⊢φ⇒ψ⇒ξ Γ⊢φ) Γ⊢ψ

MP3 : Γ ⊢ φ ⇒ ψ ⇒ ξ ⇒ θ →
      Γ ⊢ φ →
      Γ ⊢ ψ →
      Γ ⊢ ξ →
      ------
      Γ ⊢ θ

MP3 Γ⊢φ⇒ψ⇒ξ⇒θ Γ⊢φ Γ⊢ψ Γ⊢ξ = MP (MP2 Γ⊢φ⇒ψ⇒ξ⇒θ Γ⊢φ Γ⊢ψ) Γ⊢ξ
```

We need to convert an arbitrary formula `φ` to a formula `ψ` in the implication fragment
s.t. the two are provably equivalent:

```
help0 : Γ ⊢ φ ⇔ ψ → Γ ⊢ φ ⇒ ψ
help0 Γ⊢φ⇔ψ = MP E1 Γ⊢φ⇔ψ

help1 : Γ ⊢ φ ⇔ ψ → Γ ⊢ ψ ⇒ φ
help1 Γ⊢φ⇔ψ = MP E2 Γ⊢φ⇔ψ

help2 : Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ ⇒ φ → Γ ⊢ φ ⇔ ψ
help2 Γ⊢φ⇒ψ Γ⊢ψ⇒φ = MP (MP E3 Γ⊢φ⇒ψ) Γ⊢ψ⇒φ

trans-⇒ : Γ ⊢ φ ⇒ ψ →
          Γ ⊢ ψ ⇒ ξ → 
          ---------
          Γ ⊢ φ ⇒ ξ

trans-⇒ {Γ} {φ} {ψ} {ξ} Γ⊢φ⇒ψ Γ⊢ψ⇒ξ =
  BEGIN
  have Γ · φ ⊢ φ      by Ass here
  have Γ · φ ⊢ φ ⇒ ψ  by mon-⊢ Γ⊢φ⇒ψ
  have Γ · φ ⊢ ψ      apply MP at here , back 1
  have Γ · φ ⊢ ψ ⇒ ξ  by mon-⊢ Γ⊢ψ⇒ξ
  have Γ · φ ⊢ ξ      apply MP at here , back 1
  have Γ ⊢ φ ⇒ ξ      apply DT2 at here
  END

refl-⇔ : Γ ⊢ φ ⇔ φ
refl-⇔ = help2 refl-⇒ refl-⇒

sym-⇔ : Γ ⊢ φ ⇔ ψ →
        ---------
        Γ ⊢ ψ ⇔ φ

sym-⇔ Γ⊢φ⇔ψ = help2 (help1 Γ⊢φ⇔ψ) (help0 Γ⊢φ⇔ψ)

trans-⇔ : Γ ⊢ φ ⇔ ψ →
          Γ ⊢ ψ ⇔ ξ →
          ---------
          Γ ⊢ φ ⇔ ξ

trans-⇔ Γ⊢φ⇔ψ Γ⊢ψ⇔ξ = help2 (trans-⇒ (help0 Γ⊢φ⇔ψ) (help0 Γ⊢ψ⇔ξ))
                            (trans-⇒ (help1 Γ⊢ψ⇔ξ) (help1 Γ⊢φ⇔ψ))

helper-⇒ : ∀ {Γ p φ ψ} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F[ p ↦ ψ ] ⇒ ξ₀ F[ p ↦ φ ] →
  Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ] →
  --------------------------------------------------------
  Γ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ⇒ ξ₁) F[ p ↦ ψ ]

helper-⇒ {Γ} {p} {φ} {ψ} ξ₀ ξ₁ ass₀ ass₁ = DT2 (DT2 goal) where

    Ξ₀ = Γ · (ξ₀ ⇒ ξ₁) F[ p ↦ φ ] · ξ₀ F[ p ↦ ψ ]

    goal =
        BEGIN
        have Ξ₀ ⊢ ξ₀ F[ p ↦ ψ ]                 by Ass here
        have Ξ₀ ⊢ ξ₀ F[ p ↦ ψ ] ⇒ ξ₀ F[ p ↦ φ ] by mon2-⊢ ass₀
        have Ξ₀ ⊢ ξ₀ F[ p ↦ φ ]                 apply MP at here , back 1
        have Ξ₀ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ]          by Ass back 1
        have Ξ₀ ⊢ ξ₁ F[ p ↦ φ ]                 apply MP at here , back 1
        have Ξ₀ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ] by mon2-⊢ ass₁
        have Ξ₀ ⊢ ξ₁ F[ p ↦ ψ ]                 apply MP at here , back 1
        END

helper-⇔ : ∀ {Γ p φ ψ} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F[ p ↦ φ ] ⇔ ξ₀ F[ p ↦ ψ ] →
  Γ ⊢ ξ₁ F[ p ↦ φ ] ⇔ ξ₁ F[ p ↦ ψ ] →
  ------------------------------------------------
  Γ ⊢ (ξ₀ ⇔ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ⇔ ξ₁) F[ p ↦ ψ ]

helper-⇔ {Γ} {p} {φ} {ψ} ξ₀ ξ₁ ass₀ ass₁
  = DT2 (help2 goal₀ goal₁) where

  Γ₀ = Γ · (ξ₀ ⇔ ξ₁) F[ p ↦ φ ]

  goal₀ =
    BEGIN
    have Γ ⊢ ξ₀ F[ p ↦ ψ ] ⇒ ξ₀ F[ p ↦ φ ]                by help1 ass₀
    have Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ]                by help0 ass₁
    have Γ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ⇒ ξ₁) F[ p ↦ ψ ]  apply helper-⇒ ξ₀ ξ₁ at back 1 , here

    have Γ₀ ⊢ (ξ₀ ⇔ ξ₁) F[ p ↦ φ ]                        by Ass here
    have Γ₀ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ]                        apply help0 at here
    have Γ₀ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ⇒ ξ₁) F[ p ↦ ψ ] apply mon-⊢ at back 2
    have Γ₀ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ ψ ]                        apply MP at here , back 1
    END

  goal₁ =
    BEGIN
    have Γ ⊢ ξ₁ F[ p ↦ ψ ] ⇒ ξ₁ F[ p ↦ φ ]                by help1 ass₁
    have Γ ⊢ ξ₀ F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ]                by help0 ass₀
    have Γ ⊢ (ξ₁ ⇒ ξ₀) F[ p ↦ φ ] ⇒ (ξ₁ ⇒ ξ₀) F[ p ↦ ψ ]  apply helper-⇒ ξ₁ ξ₀ at back 1 , here

    have Γ₀ ⊢ (ξ₀ ⇔ ξ₁) F[ p ↦ φ ]                        by Ass here
    have Γ₀ ⊢ (ξ₁ ⇒ ξ₀) F[ p ↦ φ ]                        apply help1 at here
    have Γ₀ ⊢ (ξ₁ ⇒ ξ₀) F[ p ↦ φ ] ⇒ (ξ₁ ⇒ ξ₀) F[ p ↦ ψ ] apply mon-⊢ at back 2
    have Γ₀ ⊢ (ξ₁ ⇒ ξ₀) F[ p ↦ ψ ]                        apply MP at here , back 1
    END

cong-∨ : ∀ {Γ p φ ψ} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ] →
  Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ] →
  ------------------------------------------------
  Γ ⊢ (ξ₀ ∨ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]

cong-∨ {Γ} {p} {φ} {ψ} ξ₀ ξ₁ ass₀ ass₁ =
  BEGIN
  have Γ · ξ₀ F[ p ↦ φ ] ⊢ ξ₀ F[ p ↦ ψ ]          by DT1 ass₀
  have Γ · ξ₀ F[ p ↦ φ ] ⊢ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]   apply (MP D1) at here
  have Γ ⊢ ξ₀ F[ p ↦ φ ] ⇒ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]   apply DT2 at here

  have Γ · ξ₁ F[ p ↦ φ ] ⊢ ξ₁ F[ p ↦ ψ ]          by DT1 ass₁
  have Γ · ξ₁ F[ p ↦ φ ] ⊢ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]   apply (MP D2) at here
  have Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]   apply DT2 at here

  have Γ ⊢ (ξ₀ ∨ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]
    apply (MP2 D3) at back 3 , here
  END

cong-∧ : ∀ {Γ p φ ψ} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ] →
  Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ] →
  ------------------------------------------------
  Γ ⊢ (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ∧ ξ₁) F[ p ↦ ψ ]

cong-∧ {Γ} {p} {φ} {ψ} ξ₀ ξ₁ ass₀ ass₁ =
  BEGIN
  have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₀ F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ]   by mon-⊢ ass₀
  have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₀ F[ p ↦ φ ]                   by MP C1 (Ass here) 
  have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₀ F[ p ↦ ψ ]                   apply MP at back 1 , here

  have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ]   by mon-⊢ ass₁
  have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₁ F[ p ↦ φ ]                   by MP C2 (Ass here)
  have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₁ F[ p ↦ ψ ]                   apply MP at back 1 , here

  have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ (ξ₀ ∧ ξ₁) F[ p ↦ ψ ]            apply MP2 C3 at back 3 , here
  have Γ ⊢ (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ∧ ξ₁) F[ p ↦ ψ ]            apply DT2 at here
  END

cong-↔ : ∀ ξ p →
  Γ ⊢ φ ⇔ ψ →
  -------------------------------
  Γ ⊢ ξ F[ p ↦ φ ] ⇔ ξ F[ p ↦ ψ ]

cong-↔ ⊥ p Γ⊢φ⇔ψ = refl-⇔

cong-↔ ⊤ p Γ⊢φ⇔ψ = refl-⇔

cong-↔ (` q) p Γ⊢φ⇔ψ
  with p ≡? q
... | yes _ = Γ⊢φ⇔ψ
... | no _ = refl-⇔

cong-↔ {Γ} {φ} {ψ} (¬ ξ) p Γ⊢φ⇔ψ
  with cong-↔ ξ p Γ⊢φ⇔ψ
... | Γ⊢ξ[p↦φ]⇔ξ[p↦ψ]
  with help0 Γ⊢ξ[p↦φ]⇔ξ[p↦ψ] |
       help1 Γ⊢ξ[p↦φ]⇔ξ[p↦ψ]
... | Γ⊢ξ[p↦φ]⇒ξ[p↦ψ] | Γ⊢ξ[p↦ψ]⇒ξ[p↦φ]
  = help2 Γ⊢¬ξ[p↦φ]⇒¬ξ[p↦ψ] Γ⊢¬ξ[p↦ψ]⇒¬ξ[p↦φ] where

    Γ⊢¬ξ[p↦φ]⇒¬ξ[p↦ψ] : Γ ⊢ ¬ ξ F[ p ↦ φ ] ⇒ ¬ ξ F[ p ↦ ψ ]
    Γ⊢¬ξ[p↦φ]⇒¬ξ[p↦ψ] = MP contraposition Γ⊢ξ[p↦ψ]⇒ξ[p↦φ]
    
    Γ⊢¬ξ[p↦ψ]⇒¬ξ[p↦φ] : Γ ⊢ ¬ ξ F[ p ↦ ψ ] ⇒ ¬ ξ F[ p ↦ φ ]
    Γ⊢¬ξ[p↦ψ]⇒¬ξ[p↦φ] = MP contraposition Γ⊢ξ[p↦φ]⇒ξ[p↦ψ]

cong-↔ (ξ₀ ∨ ξ₁) p Γ⊢φ⇔ψ
  with cong-↔ ξ₀ p Γ⊢φ⇔ψ | cong-↔ ξ₁ p Γ⊢φ⇔ψ
... | Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
  with help0 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | help1 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] |
       help0 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ] | help1 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
... | Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] | Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ]
    | Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ] | Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ]
  = help2 (cong-∨ ξ₀ ξ₁ Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ])
          (cong-∨ ξ₀ ξ₁ Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ] Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ])

cong-↔ (ξ₀ ∧ ξ₁) p Γ⊢φ⇔ψ
  with cong-↔ ξ₀ p Γ⊢φ⇔ψ | cong-↔ ξ₁ p Γ⊢φ⇔ψ
... | Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
  with help0 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | help1 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] |
       help0 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ] | help1 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
... | Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] | Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ]
    | Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ] | Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ]
  = help2 (cong-∧ ξ₀ ξ₁ Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ])
          (cong-∧ ξ₀ ξ₁ Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ] Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ])

cong-↔ (ξ₀ ⇒ ξ₁) p Γ⊢φ⇔ψ 
  with cong-↔ ξ₀ p Γ⊢φ⇔ψ | cong-↔ ξ₁ p Γ⊢φ⇔ψ
... | Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
  with help0 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | help1 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] |
       help0 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ] | help1 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
... | Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] | Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ]
    | Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ] | Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ]
  = help2 (helper-⇒ ξ₀ ξ₁ Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ] Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ])
          (helper-⇒ ξ₀ ξ₁ Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ])

cong-↔ (ξ₀ ⇔ ξ₁) p Γ⊢φ⇔ψ
  with cong-↔ ξ₀ p Γ⊢φ⇔ψ | cong-↔ ξ₁ p Γ⊢φ⇔ψ
... | Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
  = help2 (helper-⇔ ξ₀ ξ₁ Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ])
          (helper-⇔ ξ₀ ξ₁ (sym-⇔ Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ]) (sym-⇔ Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]))
```

```
-- this is actually false;
-- turn it into an exercise
-- cong-alt : ∀ ξ p →
--   Γ ⊢ φ ⇔ ψ →
--   -------------------------------
--   Γ ⊢ φ F[ p ↦ ξ ] ⇔ ψ F[ p ↦ ξ ]

```

```
cong2-∨ : ∀ {Γ p q φ φ′ ψ ψ′} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F2[ p , q ↦ φ , ψ ] ⇒ ξ₀ F2[ p , q ↦ φ′ , ψ′ ] →
  Γ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ] ⇒ ξ₁ F2[ p , q ↦ φ′ , ψ′ ] →
  -------------------------------------------------------------------
  Γ ⊢ (ξ₀ ∨ ξ₁) F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ∨ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]

cong2-∨ {Γ} {p} {q} {φ} {φ′} {ψ} {ψ′} ξ₀ ξ₁ ass₀ ass₁ =
  BEGIN
  have Γ · ξ₀ F2[ p , q ↦ φ , ψ ] ⊢ ξ₀ F2[ p , q ↦ φ′ , ψ′ ]        by DT1 ass₀
  have Γ · ξ₀ F2[ p , q ↦ φ , ψ ] ⊢ (ξ₀ ∨ ξ₁) F2[ p , q ↦ φ′ , ψ′ ] apply (MP D1) at here
  have Γ ⊢ ξ₀ F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ∨ ξ₁) F2[ p , q ↦ φ′ , ψ′ ] apply DT2 at here

  have Γ · ξ₁ F2[ p , q ↦ φ , ψ ] ⊢ ξ₁ F2[ p , q ↦ φ′ , ψ′ ]        by DT1 ass₁
  have Γ · ξ₁ F2[ p , q ↦ φ , ψ ] ⊢ (ξ₀ ∨ ξ₁) F2[ p , q ↦ φ′ , ψ′ ] apply (MP D2) at here
  have Γ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ∨ ξ₁) F2[ p , q ↦ φ′ , ψ′ ] apply DT2 at here

  have Γ ⊢ (ξ₀ ∨ ξ₁) F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ∨ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]
    apply (MP2 D3) at back 3 , here
  END

cong2-∧ : ∀ {Γ p q φ φ′ ψ ψ′} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F2[ p , q ↦ φ , ψ ] ⇒ ξ₀ F2[ p , q ↦ φ′ , ψ′ ] →
  Γ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ] ⇒ ξ₁ F2[ p , q ↦ φ′ , ψ′ ] →
  -------------------------------------------------------------------
  Γ ⊢ (ξ₀ ∧ ξ₁) F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ∧ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]

cong2-∧ {Γ} {p} {q} {φ} {φ′} {ψ} {ψ′} ξ₀ ξ₁ ass₀ ass₁ =
  BEGIN
  have Γ₀ ⊢ ξ₀ F2[ p , q ↦ φ , ψ ] ⇒ ξ₀ F2[ p , q ↦ φ′ , ψ′ ]               by mon-⊢ ass₀
  have Γ₀ ⊢ ξ₀ F2[ p , q ↦ φ , ψ ]                                          by MP C1 (Ass here) 
  have Γ₀ ⊢ ξ₀ F2[ p , q ↦ φ′ , ψ′ ]                                        apply MP at back 1 , here

  have Γ₀ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ] ⇒ ξ₁ F2[ p , q ↦ φ′ , ψ′ ]               by mon-⊢ ass₁
  have Γ₀ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ]                                          by MP C2 (Ass here)
  have Γ₀ ⊢ ξ₁ F2[ p , q ↦ φ′ , ψ′ ]                                        apply MP at back 1 , here

  have Γ₀ ⊢ (ξ₀ ∧ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]                                 apply MP2 C3 at back 3 , here
  have Γ ⊢ (ξ₀ ∧ ξ₁) F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ∧ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]  apply DT2 at here
  END where Γ₀ = Γ · (ξ₀ ∧ ξ₁) F2[ p , q ↦ φ , ψ ]

cong2-⇒ : ∀ {Γ p q φ φ′ ψ ψ′} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F2[ p , q ↦ φ′ , ψ′ ] ⇒ ξ₀ F2[ p , q ↦ φ , ψ ] → -- !
  Γ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ] ⇒ ξ₁ F2[ p , q ↦ φ′ , ψ′ ] →
  -------------------------------------------------------------------
  Γ ⊢ (ξ₀ ⇒ ξ₁) F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ⇒ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]

cong2-⇒ {Γ} {p} {q} {φ} {φ′} {ψ} {ψ′} ξ₀ ξ₁ ass₀ ass₁ = DT2 (DT2 goal) where

    Ξ₀ = Γ · (ξ₀ ⇒ ξ₁) F2[ p , q ↦ φ , ψ ] · ξ₀ F2[ p , q ↦ φ′ , ψ′ ]

    goal =
      BEGIN
      have Ξ₀ ⊢ ξ₀ F2[ p , q ↦ φ′ , ψ′ ]                          by Ass here
      have Ξ₀ ⊢ ξ₀ F2[ p , q ↦ φ′ , ψ′ ] ⇒ ξ₀ F2[ p , q ↦ φ , ψ ] by mon2-⊢ ass₀
      have Ξ₀ ⊢ ξ₀ F2[ p , q ↦ φ , ψ ]                            apply MP at here , back 1
      have Ξ₀ ⊢ (ξ₀ ⇒ ξ₁) F2[ p , q ↦ φ , ψ ]                     by Ass back 1
      have Ξ₀ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ]                            apply MP at here , back 1
      have Ξ₀ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ] ⇒ ξ₁ F2[ p , q ↦ φ′ , ψ′ ] by mon2-⊢ ass₁
      have Ξ₀ ⊢ ξ₁ F2[ p , q ↦ φ′ , ψ′ ]                          apply MP at here , back 1
      END

cong2-⇔ : ∀ {Γ p q φ φ′ ψ ψ′} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F2[ p , q ↦ φ , ψ ] ⇒ ξ₀ F2[ p , q ↦ φ′ , ψ′ ] →
  Γ ⊢ ξ₁ F2[ p , q ↦ φ , ψ ] ⇒ ξ₁ F2[ p , q ↦ φ′ , ψ′ ] →
  Γ ⊢ ξ₀ F2[ p , q ↦ φ′ , ψ′ ] ⇒ ξ₀ F2[ p , q ↦ φ , ψ ] →
  Γ ⊢ ξ₁ F2[ p , q ↦ φ′ , ψ′ ] ⇒ ξ₁ F2[ p , q ↦ φ , ψ ] →
  -------------------------------------------------------------------
  Γ ⊢ (ξ₀ ⇔ ξ₁) F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ⇔ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]

cong2-⇔ {Γ} {p} {q} {φ} {φ′} {ψ} {ψ′} ξ₀ ξ₁ ass₀ ass₁ ass₂ ass₃ = DT2 (help2 goal0 goal1) where

  Ξ = Γ · (ξ₀ ⇔ ξ₁) F2[ p , q ↦ φ , ψ ]

  goal0 =
    BEGIN
    have Ξ ⊢ (ξ₀ ⇔ ξ₁) F2[ p , q ↦ φ , ψ ]                                    by Ass here
    have Ξ ⊢ (ξ₀ ⇒ ξ₁) F2[ p , q ↦ φ , ψ ]                                    apply help0 at here
    have Ξ ⊢ (ξ₀ ⇒ ξ₁) F2[ p , q ↦ φ , ψ ] ⇒ (ξ₀ ⇒ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]  by mon-⊢ (cong2-⇒ ξ₀ ξ₁ ass₂ ass₁)
    have Ξ ⊢ (ξ₀ ⇒ ξ₁) F2[ p , q ↦ φ′ , ψ′ ]                                  apply MP at here , back 1
    END

  goal1 =
    BEGIN
    have Ξ ⊢ (ξ₀ ⇔ ξ₁) F2[ p , q ↦ φ , ψ ]                                    by Ass here
    have Ξ ⊢ (ξ₁ ⇒ ξ₀) F2[ p , q ↦ φ , ψ ]                                    apply help1 at here
    have Ξ ⊢ (ξ₁ ⇒ ξ₀) F2[ p , q ↦ φ , ψ ] ⇒ (ξ₁ ⇒ ξ₀) F2[ p , q ↦ φ′ , ψ′ ]  by mon-⊢ (cong2-⇒ ξ₁ ξ₀ ass₃ ass₀)
    have Ξ ⊢ (ξ₁ ⇒ ξ₀) F2[ p , q ↦ φ′ , ψ′ ]                                  apply MP at here , back 1
    END

```

```
cong2-↔-left : ∀ {φ ψ φ′ ψ′} ξ p q →
  Γ ⊢ φ ⇔ φ′ →
  Γ ⊢ ψ ⇔ ψ′ →
  ---------------------------------------------------
  Γ ⊢ ξ F2[ p , q ↦ φ , ψ ] ⇒ ξ F2[ p , q ↦ φ′ , ψ′ ]

cong2-↔-right : ∀ {φ ψ φ′ ψ′} ξ p q →
  Γ ⊢ φ ⇔ φ′ →
  Γ ⊢ ψ ⇔ ψ′ →
  ---------------------------------------------------
  Γ ⊢ ξ F2[ p , q ↦ φ′ , ψ′ ] ⇒ ξ F2[ p , q ↦ φ , ψ ]

cong2-↔-left ⊥ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ = refl-⇒

cong2-↔-left ⊤ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ = refl-⇒

cong2-↔-left (` r) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with p ≡? r | inspect (q ≡? r)
... | yes _ | _ = help0 Γ⊢φ⇔φ′
... | no _ | it (yes _) eql rewrite eql = help0 Γ⊢ψ⇔ψ′
... | no _ | it (no _) eql rewrite eql = refl-⇒

cong2-↔-left (¬ ξ) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-right ξ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ -- !
... | ass = MP contraposition ass

cong2-↔-left (ξ₀ ∨ ξ₁) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-left ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-left ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
... | ass₀ | ass₁ = cong2-∨ ξ₀ ξ₁ ass₀ ass₁

cong2-↔-left (ξ₀ ∧ ξ₁) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-left ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-left ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
... | ass₀ | ass₁ = cong2-∧ ξ₀ ξ₁ ass₀ ass₁

cong2-↔-left (ξ₀ ⇒ ξ₁) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-right ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ | -- !
       cong2-↔-left ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
... | ass₀ | ass₁ = cong2-⇒ ξ₀ ξ₁ ass₀ ass₁

cong2-↔-left (ξ₀ ⇔ ξ₁) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-left ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-left ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-right ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-right ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
... | ass₀ | ass₁ | ass₂ | ass₃ = cong2-⇔ ξ₀ ξ₁ ass₀ ass₁ ass₂ ass₃

cong2-↔-right ⊥ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ = refl-⇒

cong2-↔-right ⊤ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ = refl-⇒

cong2-↔-right (` r) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with p ≡? r | inspect (q ≡? r)
... | yes _ | _ = help1 Γ⊢φ⇔φ′
... | no _ | it (yes _) eql rewrite eql = help1 Γ⊢ψ⇔ψ′
... | no _ | it (no _) eql rewrite eql = refl-⇒

cong2-↔-right (¬ ξ) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-left ξ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ -- !
... | ass = MP contraposition ass

cong2-↔-right (ξ₀ ∨ ξ₁) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-right ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-right ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
... | ass₀ | ass₁ = cong2-∨ ξ₀ ξ₁ ass₀ ass₁

cong2-↔-right (ξ₀ ∧ ξ₁) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-right ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-right ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
... | ass₀ | ass₁ = cong2-∧ ξ₀ ξ₁ ass₀ ass₁

cong2-↔-right (ξ₀ ⇒ ξ₁) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-left ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ | -- !
       cong2-↔-right ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
... | ass₀ | ass₁ = cong2-⇒ ξ₀ ξ₁ ass₀ ass₁

cong2-↔-right (ξ₀ ⇔ ξ₁) p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
  with cong2-↔-right ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-right ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-left ξ₀ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ |
       cong2-↔-left ξ₁ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′
... | ass₀ | ass₁ | ass₂ | ass₃ = cong2-⇔ ξ₀ ξ₁ ass₀ ass₁ ass₂ ass₃

cong2-↔ : ∀ {φ ψ φ′ ψ′} ξ p q →
  Γ ⊢ φ ⇔ φ′ →
  Γ ⊢ ψ ⇔ ψ′ →
  ---------------------------------------------------
  Γ ⊢ ξ F2[ p , q ↦ φ , ψ ] ⇔ ξ F2[ p , q ↦ φ′ , ψ′ ]

cong2-↔  ξ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′ = help2 (cong2-↔-left ξ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′) (cong2-↔-right ξ p q Γ⊢φ⇔φ′ Γ⊢ψ⇔ψ′)

equiv-¬ : Γ ⊢ ¬ φ ⇔ (φ ⇒ ⊥)
equiv-¬ = help2 N1 N2

equiv-∨-left : Γ ⊢ (φ ∨ ψ) ⇒ (φ ⇒ ⊥) ⇒ ψ
equiv-∨-left {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ∨ ψ ⊢ (φ ⇒ ⊥) ⇒ φ ⇒ ψ    by B2
  have Γ · φ ∨ ψ · φ ⇒ ⊥ ⊢ φ ⇒ ψ      apply DT1 at here
  have Γ · φ ∨ ψ · φ ⇒ ⊥ ⊢ ψ ⇒ ψ      by refl-⇒
  have Γ · φ ∨ ψ · φ ⇒ ⊥ ⊢ φ ∨ ψ      by Ass back 1
  have Γ · φ ∨ ψ · φ ⇒ ⊥ ⊢ ψ          apply MP3 D3 at back 2 , back 1 , here
  have Γ · φ ∨ ψ ⊢ (φ ⇒ ⊥) ⇒ ψ        apply DT2 at here
  have Γ ⊢ (φ ∨ ψ) ⇒ ((φ ⇒ ⊥) ⇒ ψ)    apply DT2 at here
  END

equiv-∨-right : Γ ⊢ ((φ ⇒ ⊥) ⇒ ψ) ⇒ φ ∨ ψ
equiv-∨-right {Γ} {φ} {ψ} =
  BEGIN
  have Γ · (φ ⇒ ⊥) ⇒ ψ · φ ⇒ ⊥ ⊢ φ ⇒ ⊥        by Ass here
  have Γ · (φ ⇒ ⊥) ⇒ ψ · φ ⇒ ⊥ ⊢ (φ ⇒ ⊥) ⇒ ψ  by Ass back 1
  have Γ · (φ ⇒ ⊥) ⇒ ψ · φ ⇒ ⊥ ⊢ ψ            apply MP at here , back 1
  have Γ · (φ ⇒ ⊥) ⇒ ψ · φ ⇒ ⊥ ⊢ φ ∨ ψ        apply MP D2 at here
  have Γ · (φ ⇒ ⊥) ⇒ ψ ⊢ (φ ⇒ ⊥) ⇒ φ ∨ ψ      apply DT2 at here

  have Γ · (φ ⇒ ⊥) ⇒ ψ ⊢ φ ⇒ φ ∨ ψ            by D1

  have Γ · (φ ⇒ ⊥) ⇒ ψ ⊢ φ ∨ ψ                apply MP2 B3 at here , back 1
  have Γ ⊢ ((φ ⇒ ⊥) ⇒ ψ) ⇒ φ ∨ ψ              apply DT2 at here
  END

equiv-∨ : Γ ⊢ (φ ∨ ψ) ⇔ ((φ ⇒ ⊥) ⇒ ψ)
equiv-∨ = help2 equiv-∨-left equiv-∨-right

equiv-∧-left : Γ ⊢ φ ∧ ψ ⇒ ((φ ⇒ ψ ⇒ ⊥) ⇒ ⊥)
equiv-∧-left {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ∧ ψ · φ ⇒ ψ ⇒ ⊥ ⊢ φ ∧ ψ      by Ass back 1
  have Γ · φ ∧ ψ · φ ⇒ ψ ⇒ ⊥ ⊢ φ          apply MP C1 at here
  have Γ · φ ∧ ψ · φ ⇒ ψ ⇒ ⊥ ⊢ ψ          apply MP C2 at back 1
  have Γ · φ ∧ ψ · φ ⇒ ψ ⇒ ⊥ ⊢ φ ⇒ ψ ⇒ ⊥  by Ass here
  have Γ · φ ∧ ψ · φ ⇒ ψ ⇒ ⊥ ⊢ ⊥          apply MP2 at here , back 2 , back 1
  have Γ · φ ∧ ψ ⊢ (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥        apply DT2 at here
  have Γ ⊢ φ ∧ ψ ⇒ ((φ ⇒ ψ ⇒ ⊥) ⇒ ⊥)      apply DT2 at here
  END

equiv-∧-right : Γ ⊢ ((φ ⇒ ψ ⇒ ⊥) ⇒ ⊥) ⇒ φ ∧ ψ
equiv-∧-right {Γ} {φ} {ψ} =
  BEGIN
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ · φ · ψ ⊢ φ          by Ass back 1
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ · φ · ψ ⊢ ψ          by Ass here
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ · φ · ψ ⊢ φ ∧ ψ      apply MP2 C3 at back 1 , here
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ · φ · ψ ⊢ φ ∧ ψ ⇒ ⊥  by Ass back 2
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ · φ · ψ ⊢ ⊥          apply MP at here , back 1
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ · φ ⊢ ψ ⇒ ⊥          apply DT2 at here
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ ⊢ φ ⇒ ψ ⇒ ⊥          apply DT2 at here
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ ⊢ (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥    by Ass back 1
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ ⊢ ⊥                  apply MP at here , back 1
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ · φ ∧ ψ ⇒ ⊥ ⊢ φ ∧ ψ              apply MP B1 at here
  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ ⊢ (φ ∧ ψ ⇒ ⊥) ⇒ φ ∧ ψ            apply DT2 at here

  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ ⊢ φ ∧ ψ ⇒ φ ∧ ψ                  by refl-⇒

  have Γ · (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ ⊢ φ ∧ ψ                          apply MP2 B3 at here , back 1
  have Γ ⊢ ((φ ⇒ ψ ⇒ ⊥) ⇒ ⊥) ⇒ φ ∧ ψ                        apply DT2 at here
  END

equiv-∧ : Γ ⊢ φ ∧ ψ ⇔ ((φ ⇒ ψ ⇒ ⊥) ⇒ ⊥)
equiv-∧ = help2 equiv-∧-left equiv-∧-right
  
equiv-⇔ : Γ ⊢ (φ ⇔ ψ) ⇔ (((φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ ⊥) ⇒ ⊥)
equiv-⇔ {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ⇔ ψ ⊢ φ ⇔ ψ                          by Ass here
  have Γ · φ ⇔ ψ ⊢ φ ⇒ ψ                          apply help0 at here
  have Γ · φ ⇔ ψ ⊢ ψ ⇒ φ                          apply help1 at (back 1)
  have Γ · φ ⇔ ψ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)              apply MP2 C3 at back 1 , here
  have Γ ⊢ (φ ⇔ ψ) ⇒ (φ ⇒ ψ) ∧ (ψ ⇒ φ)            apply DT2 at here

  have Γ · (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)  by Ass here
  have Γ · (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⊢ φ ⇒ ψ              apply MP C1 at here
  have Γ · (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⊢ ψ ⇒ φ              apply MP C2 at back 1
  have Γ · (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⊢ φ ⇔ ψ              apply help2 at back 1 , here
  have Γ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⇒ (φ ⇔ ψ)            apply DT2 at here

  have Γ ⊢ (φ ⇔ ψ) ⇔ (φ ⇒ ψ) ∧ (ψ ⇒ φ)            apply help2 at there (there (back 3)) , here

  have Γ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⇔ (((φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ ⊥) ⇒ ⊥)  by equiv-∧

  have Γ ⊢ (φ ⇔ ψ) ⇔ (((φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ ⊥) ⇒ ⊥)            apply trans-⇔ at back 1 , here
  END

equiv-⊤ : Γ ⊢ ⊤ ⇔ φ ⇒ φ
equiv-⊤ {Γ} {φ} =
  BEGIN
  have Γ · ⊤ ⊢ φ ⇒ φ    by refl-⇒
  have Γ ⊢ ⊤ ⇒ φ ⇒ φ    apply DT2 at here 

  have Γ · φ ⇒ φ ⊢ ⊤    by T1
  have Γ ⊢ (φ ⇒ φ) ⇒ ⊤  apply DT2 at here 

  have Γ ⊢ ⊤ ⇔ φ ⇒ φ    apply help2 at back 2 , here
  END

-- notice that we need only the ψ ⇒ φ direction
convert : ∀ φ → ∃[ ψ ] Formula[⇒,⊥] ψ × ∅ ⊢ φ ⇔ ψ

convert ⊥ = _ , ⊥ , refl-⇔

convert ⊤ = _ , ` p₀ ⇒ ` p₀ , equiv-⊤

convert (` p) = _ , ` p , refl-⇔

convert (¬ φ)
  with convert φ
... | ψ , view-ψ , ⊢φ⇔ψ = ψ ⇒ ⊥ , view-ψ ⇒ ⊥ , (BEGIN
  have ε ⊢ ¬ φ ⇔ (φ ⇒ ⊥)      by equiv-¬
  have ε ⊢ (φ ⇒ ⊥) ⇔ (ψ ⇒ ⊥)  by cong-↔ (` p₀ ⇒ ⊥) p₀ ⊢φ⇔ψ
  have ε ⊢ ¬ φ ⇔ (ψ ⇒ ⊥)      apply trans-⇔ at back 1 , here
  END)

convert (φ ∨ ψ)
  with convert φ | convert ψ
... | φ′ , view-φ′ , ⊢φ⇔φ′
    | ψ′ , view-ψ′ , ⊢ψ⇔ψ′
    = (φ′ ⇒ ⊥) ⇒ ψ′ , (view-φ′ ⇒ ⊥) ⇒ view-ψ′ , (BEGIN
    have ε ⊢ φ ∨ ψ ⇔ ((φ ⇒ ⊥) ⇒ ψ)            by equiv-∨
    have ε ⊢ ((φ ⇒ ⊥) ⇒ ψ) ⇔ ((φ′ ⇒ ⊥) ⇒ ψ′)  by cong2-↔ ((` p₀ ⇒ ⊥) ⇒ ` p₁) p₀ p₁ ⊢φ⇔φ′ ⊢ψ⇔ψ′
    have ε ⊢ φ ∨ ψ ⇔ (φ′ ⇒ ⊥) ⇒ ψ′            apply trans-⇔ at back 1 , here
    END)

convert (φ ∧ ψ)
  with convert φ | convert ψ
... | φ′ , view-φ′ , ⊢φ⇔φ′
    | ψ′ , view-ψ′ , ⊢ψ⇔ψ′
    = (φ′ ⇒ ψ′ ⇒ ⊥) ⇒ ⊥ , ((view-φ′ ⇒ (view-ψ′ ⇒ ⊥)) ⇒ ⊥) , (BEGIN
    have ε ⊢ φ ∧ ψ ⇔ (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥              by equiv-∧
    have ε ⊢ (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ ⇔ (φ′ ⇒ ψ′ ⇒ ⊥) ⇒ ⊥  by cong2-↔ ((` p₀ ⇒ ` p₁ ⇒ ⊥) ⇒ ⊥) p₀ p₁ ⊢φ⇔φ′ ⊢ψ⇔ψ′
    have ε ⊢ φ ∧ ψ ⇔ (φ′ ⇒ ψ′ ⇒ ⊥) ⇒ ⊥            apply trans-⇔ at back 1 , here
    END)

convert (φ ⇒ ψ)
  with convert φ | convert ψ
... | φ′ , view-φ′ , ⊢φ⇔φ′
    | ψ′ , view-ψ′ , ⊢ψ⇔ψ′
    = φ′ ⇒ ψ′ , view-φ′ ⇒ view-ψ′ , cong2-↔ (` p₀ ⇒ ` p₁) p₀ p₁ ⊢φ⇔φ′ ⊢ψ⇔ψ′


convert (φ ⇔ ψ)
  with convert φ | convert ψ
... | φ′ , view-φ′ , ⊢φ⇔φ′
    | ψ′ , view-ψ′ , ⊢ψ⇔ψ′
    = (((φ′ ⇒ ψ′) ⇒ (ψ′ ⇒ φ′) ⇒ ⊥) ⇒ ⊥) ,
      (((view-φ′ ⇒ view-ψ′) ⇒ ((view-ψ′ ⇒ view-φ′) ⇒ ⊥)) ⇒ ⊥) , (BEGIN
    have ε ⊢ (φ ⇔ ψ) ⇔ (((φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ ⊥) ⇒ ⊥)
      by equiv-⇔
    have ε ⊢ (((φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ ⊥) ⇒ ⊥) ⇔ (((φ′ ⇒ ψ′) ⇒ (ψ′ ⇒ φ′) ⇒ ⊥) ⇒ ⊥)
      by cong2-↔ ((((` p₀ ⇒ ` p₁) ⇒ (` p₁ ⇒ ` p₀) ⇒ ⊥) ⇒ ⊥)) p₀ p₁ ⊢φ⇔φ′ ⊢ψ⇔ψ′
    have ε ⊢ (φ ⇔ ψ) ⇔ (((φ′ ⇒ ψ′) ⇒ (ψ′ ⇒ φ′) ⇒ ⊥) ⇒ ⊥)
      apply trans-⇔ at back 1 , here
    END)
```

# Completeness for the full fragment {#completeness}



```
weak-completeness : ε ⊨ φ → ε ⊢ φ
weak-completeness {φ} ⊨φ
  with convert φ
... | ψ , view-ψ , ⊢φ⇔ψ
  with help0 ⊢φ⇔ψ | help1 ⊢φ⇔ψ
... | ⊢φ⇒ψ | ⊢ψ⇒φ
  with soundness ⊢φ⇒ψ
... | ⊨φ⇒ψ 
  with modus-ponens φ ψ ⊨φ⇒ψ ⊨φ
... | ⊨ψ = ⊢φ where

  ⊢ψ : ε ⊢ ψ
  ⊢ψ = weak-completeness1 view-ψ ⊨ψ

  ⊢φ : ε ⊢ φ
  ⊢φ = MP ⊢ψ⇒φ ⊢ψ
```


The following is the milestone of this chapter:

```
strong-completeness :
  Δ ⊨ φ →
  -----
  Δ ⊢ φ

strong-completeness {Δ} {φ} = begin→
  Δ ⊨ φ
    →⟨ longSemDT1 ⟩
  ε ⊨ Δ Imply φ
    →⟨ weak-completeness ⟩
  ε ⊢ Δ Imply φ
    →⟨ longDT ⟩
  Δ ⊢ φ
  ∎→
```