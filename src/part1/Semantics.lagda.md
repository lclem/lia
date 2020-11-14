---
title: Syntax and semantics of propositional logic 🚧
---

In this chapter we introduce the syntax of propositional logic.

```
{-# OPTIONS --allow-unsolved-metas  #-}
open import part0.Naturals using (ℕ)

module part1.Semantics (n : ℕ) where
open import part0.index public 
```

# Syntax

## Propositions {#prop-var}

The main building blocks of propositional logic are *propositional variables* $p, q, \dots$ (a.k.a. propositions),
and logical connectives (to be introduced in the next section).
Propositional variables can be implemented in a variety of ways,
such as strings "p", "q",...;
numbers 0, 1, ...; and many more.
Any such concrete representation will do,
provided that

* We can decide whether two given propositions are equal, and
* We can enumerate all propositions.

Our choice is to represent propositional variables with the datatype `Fin` of [finite sets](/part0/Fin).
The module parameter `n : ℕ` allows us to name a fixed but arbitrary number of distinct propositions,
leading to the following definition (we omit the type annotation `Set`).

```
PropName = Fin (3 + n)
```

We use `p`, `q`, and `r` as generic variable names.
In examples, we use `p₀`, `p₁`, and `p₂` as the following concrete variables [^10+n]:

```
variable
  p : PropName

p₀ p₁ p₂ : PropName
p₀ = fzero
p₁ = fsuc fzero 
p₂ = fsuc (fsuc fzero)
```

[^10+n]:
    With the simpler and perhaps more natural definition `PropName = Fin n`
    we would not be able to name any specific proposition such as `p = fzero`
    since `n` is arbitrary and in particular it could be `0`,
    i.e., there could be no proposition at all.

Since propositions are modelled with `Fin`,
they inherit all the properties of the latter.
In particular, they enjoy decidable equality as initially required,

```
_ : p₀ ≡? p₀ ≡ yes
_  = refl

_ : p₀ ≡? p₁ ≡ no
_  = refl
```

and they can also be enumerated:

```
propNames : PropName *
propNames = enum

findPropName : ∀ p → p ∈ propNames
findPropName = find
```

For example, the first variable in the enumeration is `p`
and the second is `q`:

```
_ : findPropName p₀ ≡ here
_ = refl

_ : findPropName p₁ ≡ there here
_ = refl
```

## Formulas

Formulas of propositional logic are constructed according to the following abstract syntax:

  $$ \varphi, \psi ∷\equiv p \mid \bot \mid \top \mid \neg p \mid \varphi \land \psi \mid \varphi \lor \psi \mid \varphi \Rightarrow \psi \mid \varphi \Leftrightarrow \psi. $$

In other words, a formula is either

* a propositional variable $p$, or
* the *false* constant $\bot$ (pronounced "bottom"), or
* the *true* constant $\top$ (pronoounced "top"), or
* the *negation* $\neg \varphi$ of a formula $\varphi$, or
* the *conjunction* $\varphi \land \psi$ of two formulas $\varphi, \psi$, or
* the *disjunction* $\varphi \lor \psi$ of two formulas $\varphi, \psi$, or
* the *implication*[^implication-symbol] $\varphi \Rightarrow \psi$ of two formulas $\varphi, \psi$, or
* the *bi-implication* $\varphi \Leftrightarrow \psi$ of two formulas $\varphi, \psi$.

[^implication-symbol]: Other commonly used symbols for implication are "$\to$"
(which conflicts with Agda's function space constructor `→` and thus must be avoided),
and the old-fashioned "$\supset$" (which conflicts with common sense,
since in terms of the subset relation, and implication is more akin to "$⊆$").

This straightforwardly translates to the following inductive type:

```
data Formula : Set where
    ⊥ ⊤ : Formula
    `_ : (p : PropName) → Formula
    ¬_ : (φ : Formula) → Formula
    _∧_ _∨_ _⇒_ _⇔_ : (φ ψ : Formula) → Formula
```

Note that there is a slight notation overload for variables `` ` p`` w.r.t. the pure mathematical syntax $p$
since we have to explicitly name the `` `_ `` constructor. The syntax for the other connectives is identical.

We follow standard notational conventions and assume that `¬` is the operator with the highest priority
(i.e., it binds tighter than any other operator),
followed by `∧`, `∨` and `⇒`, and `⇔`:

```
infix 100 `_
infix 99 ¬_
infixr 98 _∧_
infixr 97 _∨_ _⇒_
infixr 96 _⇔_
```

All binary operators are right associative.
For instance, the formula

```
φ₀ = ` p₀ ∨ ¬ ` p₀ ∨ ` p₁
```

is syntactically identical to the formula

```
φ₁ = ` p₀ ∨ ((¬ ` p₀) ∨ ` p₁)
```

## Formula size

When defining functions on formulas,
a straightforward structural induction often suffices.
<!-- as in `props` [above](#occurring-propositions) -->
However, this is not always the case, and for more complicated recursive definitions
we need to use other forms of recursion,
such as [well-founded recursion](/part0/wf).
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

As an exercise, we observe the following two inequalities satisfied by `size`.

!exercise(#exercise:size-neg)(`size-¬`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Prove that !ref(size) satisfies the following two inequalities:

```
size-¬ : ∀ φ → size φ ≤ size (¬ φ)
size-¬¬ : ∀ φ → size φ ≤ size (¬ ¬ φ)
```

(This will be used in the chapter on [Normal Forms](/part1/NormalForms).)

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
size-¬ _ = n≤sucn
size-¬¬ φ = trans-≤ (size-¬ φ) (size-¬ (¬ φ)) 
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Equality

From time to time we need to check whether two formulas are syntactically equal,
i.e., are the very same formula.
For example, `` ` p ∨ ` q`` is syntactically equal to itself,
but it is different from `` ` q ∨ ` p``.

A naïve way to decide equality would be to list all the 8 × 8 = 64 pairs of constructors,

    instance eqFormula : Eq (Formula)
    _≡?_ {{eqFormula}} = go where
      go : ∀ φ ψ → Dec (φ ≡ ψ)
      go ⊤ ⊤ = yes {proof = refl}
      go ⊤ ⊥ = no {proof = λ ()}
      go ⊤ (` _) = no {proof = λ ()}
    ...

which is not practical [^no-split-on-catchall].
We will follow another, more interesting route.

1. First, we create an enumeration for the logical connectives,
for which we can easily prove decidability of equality.

2. Then, we injectively map formulas to labelled trees,
for which decidable equality is easier to prove [^dec-eq-reference].

[^no-split-on-catchall]:
    The issue is that Agda does not perform splits on a catch-all pattern `_`,
    thus preventing the following intuitive linear-sized code from working:
  
        instance eqFormula : Eq (Formula)
        _≡?_ {{eqFormula}} = go where
          go : ∀ φ ψ → Dec (φ ≡ ψ)
          go ⊤ ⊤ = yes {proof = refl}
          go ⊤ _ = no {proof = λ ()}
        ...
    This seems to be an often-made [complaint](https://github.com/agda/agda/issues/4804) about Agda.

[^dec-eq-reference]: We present a solution inspired from a discussion on
[stackoverflow](https://stackoverflow.com/questions/45150324/decidable-equality-in-agda-with-less-than-n2-cases).

**Step 1**.
We begin by defining an enumeration type for the formula constructors (connectives).

```
data Connective : Set where
  True False Not And Or Implies Iff : Connective
```

We can injectively map elements of `Connective` to the natural numbers `ℕ` in the obvious way.

```
c2ℕ : Connective → ℕ
c2ℕ True = 0
c2ℕ False = 1
c2ℕ Not = 2
c2ℕ And = 3
c2ℕ Or = 4
c2ℕ Implies = 5
c2ℕ Iff = 6
```

Thanks to pattern matching,
we only need to consider 7 cases (linearly many in the number of constructors of `Formula`)
to show that `c2ℕ` is injective:

```
c2ℕ-inj : Injective c2ℕ
c2ℕ-inj True True _ = refl
c2ℕ-inj False False _ = refl
c2ℕ-inj Not Not _ = refl
c2ℕ-inj And And _ = refl
c2ℕ-inj Or Or _ = refl
c2ℕ-inj Implies Implies _ = refl
c2ℕ-inj Iff Iff _ = refl
```

Since equality is decidable on natural numbers `ℕ`
and `Connective` maps injectively to `ℕ`,
equality is decidable for `Connective` as well.

```
instance eqConnective : Eq Connective
_≡?_ {{eqConnective}} = go where

  go : ∀ C1 C2 → Dec (C1 ≡ C2)
  go C1 C2 with c2ℕ C1 ≡? c2ℕ C2
  -- by injectivity
  ... | yes {eq} = yes {proof = c2ℕ-inj C1 C2 eq}
  -- by functionality
  ... | no {neq} = no {proof = λ{refl → neq refl}}
```

**Step 2**.
We now injectively map formulas to `Connective ⊎ PropName`-labelled trees.
Since `Connective` and `PropName` have decidable equality,
so does their tagged union `Connective ⊎ VarName`.

```
FormulaTree = Tree (Connective ⊎ PropName)
```

We map formulas to trees by structural induction as follows:

```
Formula2Tree : Formula → FormulaTree
Formula2Tree ⊤ = Node (left True) ε
Formula2Tree ⊥ = Node (left False) ε
Formula2Tree (` p) = Node (right p) ε
Formula2Tree (¬ φ) = Node (left Not) ([ (Formula2Tree φ) ])
Formula2Tree (φ ∧ ψ) = Node (left And) ([ (Formula2Tree φ) (Formula2Tree ψ) ])
Formula2Tree (φ ∨ ψ) = Node (left Or) ([ (Formula2Tree φ) (Formula2Tree ψ) ])
Formula2Tree (φ ⇒ ψ) = Node (left Implies) ([ (Formula2Tree φ) (Formula2Tree ψ) ])
Formula2Tree (φ ⇔ ψ) = Node (left Iff) ([ (Formula2Tree φ) (Formula2Tree ψ) ])
```

!exercise(#exercise:Formula2Tree-inj)(`Formula2Tree-inj`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove that the mapping `Formula2Tree` is injective.

```
Formula2Tree-inj : Injective Formula2Tree
```

*Hint:* Exploit the fact that the list constructor `_∷_` is injective on both arguments:

```
_ = ∷-inj-left , ∷-inj-right
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
Formula2Tree-inj ⊤ ⊤ _ = refl
Formula2Tree-inj ⊥ ⊥ _ = refl
Formula2Tree-inj (` p) (` p) refl = refl
Formula2Tree-inj (¬ a) (¬ b) eql
  with Formula2Tree-inj _ _ (∷-inj-left (Node-inj-right eql))
... | refl = refl
Formula2Tree-inj (φ ∧ ψ) (φ' ∧ ψ') eql
  with Formula2Tree-inj _ _ (∷-inj-left (Node-inj-right eql)) |
       Formula2Tree-inj _ _ (∷-inj-left (∷-inj-right (Node-inj-right eql)))
... | refl | refl = refl
Formula2Tree-inj (φ ∨ ψ) (φ' ∨ ψ') eql
  with Formula2Tree-inj _ _ (∷-inj-left (Node-inj-right eql)) |
       Formula2Tree-inj _ _ (∷-inj-left (∷-inj-right (Node-inj-right eql)))
... | refl | refl = refl
Formula2Tree-inj (φ ⇒ ψ) (φ' ⇒ ψ') eql
  with Formula2Tree-inj _ _ (∷-inj-left (Node-inj-right eql)) |
       Formula2Tree-inj _ _ (∷-inj-left (∷-inj-right (Node-inj-right eql)))
... | refl | refl = refl
Formula2Tree-inj (φ ⇔ ψ) (φ' ⇔ ψ') eql
  with Formula2Tree-inj _ _ (∷-inj-left (Node-inj-right eql)) |
       Formula2Tree-inj _ _ (∷-inj-left (∷-inj-right (Node-inj-right eql)))
... | refl | refl = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

With this ingredients in hand,
we can finally show that `Formula` has decidable equality.

```
instance eqFormula : Eq Formula
_≡?_ {{eqFormula}} = go where
  
    go : ∀ φ ψ → Dec (φ ≡ ψ)
    go φ ψ with Formula2Tree φ ≡? Formula2Tree ψ
    ... | yes {eq} = yes {proof = Formula2Tree-inj _ _ eq}
    ... | no {neq} = no {proof = λ{refl → neq refl}}
```

!example(#example:equality)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We demonstrate decidability of formula equality. We have

```
_ : (` p₀ ∨ ` p₁ ≡? ` p₀ ∨ ` p₁) ≡ yes
_ = refl
```

but

```
_ : (` p₀ ∨ ` p₁ ≡? ` p₁ ∨ ` p₀) ≡ no
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

# Semantics

In this section we introduce the semantics of classical logic.

## Valuations

An *valuation* is a mapping that associates a Boolean value `𝔹` to each propositional variable.
We use `ϱ`, `ϱ'` for indicating a generic valuation.

```
Val = PropName → 𝔹

variable ϱ ϱ' : Val
```

For instance, the valuation `ϱ₀` below
assigns `ff` to `p₀` and `p₁`, and `tt` to every other variable:

```
ϱ₀ : Val
ϱ₀ = const tt [ p₀ ↦ ff ] [ p₁ ↦ ff ]
```

Since both propositions `PropName` and Boolean values `B` can be enumerated,
the same holds true for valuations `Val`,
which will be very useful to show that propositional logic is decidable.

```
vals : Val *
vals = enum

findVal : ∀ ϱ → ϱ ∈ vals
findVal = find
```

## Semantics of propositional formulas

The semantics `⟦ φ ⟧ ϱ : 𝔹` of a formula `φ : Formula` in a given valuation `ϱ : Val`
is a Boolean value (a.k.a. *truth value*) which is determined by
structural induction on `φ`:

* In the base cases `⊤` and `⊥`, the semantics is the corresponding truth value `tt`, resp., `ff`.
* In the variable case `` ` p ``, the semantics is `ϱ p` as provided by the valuation `ϱ`.
* In the negation case `¬ φ`, we inductively compute the semantics `⟦ φ ⟧ ϱ` of `φ`,
and then we apply the Boolean negation function `¬𝔹 : 𝔹 → 𝔹`.
* The remaining cases `φ ∧ ψ`, `φ ∨ ψ`, `φ ⇒ ψ`, and `φ ⇔ ψ` are similar.

Formally, we have the following definition:

```
infix 200 ⟦_⟧_

⟦_⟧_ : Formula → Val → 𝔹
⟦ ⊥ ⟧ ϱ = ff
⟦ ⊤ ⟧ ϱ = tt
⟦ ` p ⟧ ϱ = ϱ p
⟦ ¬ φ ⟧ ϱ = ¬𝔹 ⟦ φ ⟧ ϱ
⟦ φ ∧ ψ ⟧ ϱ = ⟦ φ ⟧ ϱ ∧𝔹 ⟦ ψ ⟧ ϱ
⟦ φ ∨ ψ ⟧ ϱ = ⟦ φ ⟧ ϱ ∨𝔹 ⟦ ψ ⟧ ϱ
⟦ φ ⇒ ψ ⟧ ϱ = ⟦ φ ⟧ ϱ ⇒𝔹 ⟦ ψ ⟧ ϱ
⟦ φ ⇔ ψ ⟧ ϱ = ⟦ φ ⟧ ϱ ⇔𝔹 ⟦ ψ ⟧ ϱ
```

!example(#example:semantics)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For example, we can compute the semantics of some simple formulas
(recall that both `p₀` and `p₁` evaluate to `ff` under `ϱ₀`):

```
_ : ⟦ ` p₀ ∧ ¬ ` p₁ ⟧ ϱ₀ ≡ ff
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Invariance of the semantics

In principle the semantics `⟦ φ ⟧ ϱ` of a formula `φ` depends on the valuation `ϱ`.
However, if a formula `φ` does not contain a certain proposition `p`
then clearly the value `ϱ p` of `ϱ` on `p` should not matter.
We now formalise this intuition by showing
that the semantics depends only on the propositional variables actually occurring in the formula.

We first compute the list `props φ` of occurrences of propositions in `φ`.
We proceed by structural induction on the formula:

```
props : Formula → PropName *
props ⊤ = ε
props ⊥ = ε
props (` p) = [ p ]
props (¬ φ) = props φ
props (φ ∧ ψ) = props φ ++ props ψ
props (φ ∨ ψ) = props φ ++ props ψ
props (φ ⇒ ψ) = props φ ++ props ψ
props (φ ⇔ ψ) = props φ ++ props ψ
```

Notice that `props φ` is an ordered *list* of all the occurrences of propositions in `φ`,
and thus contains duplicated elements if the same proposition appears multiple times.
For instance,

```
_ : props φ₀ ≡ [ p₀ p₀ p₁ ]
_ = refl
```

A more natural idea would be to compute the *set* $\{ p , q \}$ of all propositions occurring in `φ₀`,
i.e., without duplications (and modulo commutativity). However 1) this would be more cumbersome to represent,
and 2) the current definition is good enough for most use cases of `props`.

We say that a proposition `p` is *fresh* w.r.t. `φ`
if `p` does not occur in `props φ`.

We can now formulate the invariance of the semantics.
Intuitively, if two valuations `ϱ` and `ϱ'` agree (i.e., have the same value)
on the propositions `props φ` occurring in `φ`,
then the semantics is the same:

```
invariance : ∀ φ →
  Agree ϱ ϱ' (props φ) →
  ------------------
  ⟦ φ ⟧ ϱ ≡ ⟦ φ ⟧ ϱ'
```

!exercise(#exercise:invariance)(`invariance`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove invariance of the semantics.
*Hint*: Proceed by structural induction on formulas. In the variable case, use the assumption `Agree ϱ ϱ' (props φ)`.
In the inductive cases, use the fact that if `ϱ` and `ϱ'` agree on their value on the propositions in `φ ∧ ψ`,
then they do so on `φ`, resp., `ψ`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
invariance ⊤ agree = refl
invariance ⊥ agree = refl
invariance (` p) agree = agree here
invariance (¬ φ) agree
  rewrite invariance φ agree = refl
invariance (φ ∧ ψ) agree
  rewrite invariance φ (Agree-⊆ agree ⊆-++-left) |
          invariance ψ (Agree-⊆ agree (⊆-++-right (props φ))) = refl
invariance (φ ∨ ψ) agree
  rewrite invariance φ (Agree-⊆ agree ⊆-++-left) |
          invariance ψ (Agree-⊆ agree (⊆-++-right (props φ))) = refl
invariance (φ ⇒ ψ) agree
  rewrite invariance φ (Agree-⊆ agree ⊆-++-left) |
          invariance ψ (Agree-⊆ agree (⊆-++-right (props φ))) = refl
invariance (φ ⇔ ψ) agree
  rewrite invariance φ (Agree-⊆ agree ⊆-++-left) |
          invariance ψ (Agree-⊆ agree (⊆-++-right (props φ))) = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:coincidence)(`coincidence`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the following *concidence lemma*
stating that the semantics of a formula `φ` does not change
if we update the value of the valuation `ϱ` on a proposition `p`
not occurring in `φ`.

```
coincidence : ∀ {b} φ →
  p ∉ props φ →
  ---------------------------
  ⟦ φ ⟧ ϱ ≡ ⟦ φ ⟧ ϱ [ p ↦ b ]
```

*Hint* : Use invariance of the semantics.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
coincidence {p} {ϱ} {b} φ p∉φ = invariance φ agree where

  agree : Agree ϱ (ϱ [ p ↦ b ]) (props φ)
  agree = Agree-update-~∈ (∉→~∈ p∉φ)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Substitution lemma

A basic operation on formulas is *substitution* of a propositional variable with another formula.

```
infix 101 _F[_↦_]
_F[_↦_] : Formula → PropName → Formula → Formula
```

Intuitively, `φ F[ p ↦ ψ ]` is obtained from the formula `φ`
by replacing every occurrence of proposition `p` with `ψ`.
Substitution binds tighter than `Formula` constructors[^substitution-notation],
e.g., ¬ φ F[ p ↦ ξ ]` is interpreted as `¬ (φ F[ p ↦ ξ ])`.

[^substitution-notation]: Recall that the similar notation `_[_↦_]`
is reserved for function updates.

```
⊤ F[ _ ↦ ξ ] = ⊤
⊥ F[ p ↦ ξ ] = ⊥
(` q) F[ p ↦ ξ ] with p ≡? q
... | yes = ξ
... | no = ` q
(¬ φ) F[ p ↦ ξ ] = ¬ φ F[ p ↦ ξ ]
(φ ∧ ψ) F[ p ↦ ξ ] = φ F[ p ↦ ξ ] ∧ ψ F[ p ↦ ξ ]
(φ ∨ ψ) F[ p ↦ ξ ] = φ F[ p ↦ ξ ] ∨ ψ F[ p ↦ ξ ]
(φ ⇒ ψ) F[ p ↦ ξ ] = φ F[ p ↦ ξ ] ⇒ ψ F[ p ↦ ξ ]
(φ ⇔ ψ) F[ p ↦ ξ ] = φ F[ p ↦ ξ ] ⇔ ψ F[ p ↦ ξ ]
```

!example(#example:substitution)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For example, we have

```
_ : (` p₀ ∨ ` p₁) F[ p₁ ↦ ` p₁ ∨ ` p₂ ] ≡ ` p₀ ∨ ` p₁ ∨ ` p₂
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:parallel-substitution)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
From time to time it is useful to substitute in parallel two propositions `p` and `q` by `ψ`, resp., `ξ`,
written `φ F2[ p , q ↦ ψ , ξ ]`.
For example,

      ` p₀ ∨ ` p₁ F2[ p₀ , p₁ ↦ p₁ , p₀ ] ≡ ` p₁ ∨ ` p₀

Provide a definition of parallel substitution:

```
infix 101 _F2[_,_↦_,_]
_F2[_,_↦_,_] : Formula → PropName → PropName → Formula → Formula → Formula
```

What happens if `p ≡ q` ?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
⊥ F2[ p , q ↦ ψ , ξ ] = ⊥

⊤ F2[ p , q ↦ ψ , ξ ] = ⊤

(` r) F2[ p , q ↦ ψ , ξ ]
  with p ≡? r
... | yes = ψ
... | no
  with q ≡? r
... | yes = ξ
... | no = ` r

(¬ φ) F2[ p , q ↦ ψ , ξ ] = ¬ φ F2[ p , q ↦ ψ , ξ ]

(φ₁ ∧ φ₂) F2[ p , q ↦ ψ , ξ ] = φ₁ F2[ p , q ↦ ψ , ξ ] ∧ φ₂ F2[ p , q ↦ ψ , ξ ]

(φ₁ ∨ φ₂) F2[ p , q ↦ ψ , ξ ] = φ₁ F2[ p , q ↦ ψ , ξ ] ∨ φ₂ F2[ p , q ↦ ψ , ξ ]

(φ₁ ⇒ φ₂) F2[ p , q ↦ ψ , ξ ] = φ₁ F2[ p , q ↦ ψ , ξ ] ⇒ φ₂ F2[ p , q ↦ ψ , ξ ]

(φ₁ ⇔ φ₂) F2[ p , q ↦ ψ , ξ ] = φ₁ F2[ p , q ↦ ψ , ξ ] ⇔ φ₂ F2[ p , q ↦ ψ , ξ ]
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The main property of substitution regards its interaction with the semantics
as expressed as the following *substitution lemma*:

```
substitution : ∀ φ p ξ ϱ →
  --------------------------------------------
  ⟦ φ F[ p ↦ ξ ] ⟧ ϱ ≡ ⟦ φ ⟧ ϱ [ p ↦ ⟦ ξ ⟧ ϱ ]
```

!exercise(#exercise:substitution)(`substitution`) 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the substitution lemma.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
substitution ⊤ p ξ ϱ = refl
substitution ⊥ p ξ ϱ = refl
substitution (` q) p ξ ϱ with p ≡? q
... | yes {refl} = refl
... | no = refl
substitution (¬ φ) p ξ ϱ rewrite substitution φ p ξ ϱ = refl
substitution (φ ∧ ψ) p ξ ϱ rewrite substitution φ p ξ ϱ | substitution ψ p ξ ϱ = refl
substitution (φ ∨ ψ) p ξ ϱ rewrite substitution φ p ξ ϱ | substitution ψ p ξ ϱ = refl
substitution (φ ⇒ ψ) p ξ ϱ rewrite substitution φ p ξ ϱ | substitution ψ p ξ ϱ = refl
substitution (φ ⇔ ψ) p ξ ϱ rewrite substitution φ p ξ ϱ | substitution ψ p ξ ϱ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A *variable renaming* is a special substitution of the form ``φ F[ p ↦ ` q ]``.
It is convenient to state the substitution lemma in the special case of variable renamings:

```
renamings : ∀ φ p q ϱ →
  ------------------------------------------
  ⟦ φ F[ p ↦ ` q ] ⟧ ϱ ≡ ⟦ φ ⟧ ϱ [ p ↦ ϱ q ]
renamings φ p q ϱ = substitution φ p (` q) ϱ 
```

!exercise(#exercise:subst-id)(`subst-id`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove that a substitution `φ F[ p ↦ ξ ]` does not alter the formula `φ`
if the variable `p` does not actually appear in `φ`:

```
subst-id : ∀ φ p ξ → p ~∈ props φ → φ F[ p ↦ ξ ] ≡ φ

aux-left = ~∈-++1
aux-right = ~∈-++2
```

*Hint:* Proceed by structural induction,
using the assumption `p ~∈ props φ` in the variable case;
the two auxiliary functions `aux-left` and `aux-right` will be useful in the inductive case.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
subst-id ⊤ p ξ p~∈φ = refl
subst-id ⊥ p ξ p~∈φ = refl
subst-id (` q) p ξ p~∈φ with p ≡? q
-- contradiction
... | yes {refl} = F-elim (p~∈φ here)
... | no = refl 
subst-id (¬ φ) p ξ p~∈φ
  rewrite subst-id φ p ξ p~∈φ = refl
subst-id (φ ∧ ψ) p ξ p~∈φ
  rewrite subst-id φ p ξ (aux-left p~∈φ) |
          subst-id ψ p ξ (aux-right (props φ) p~∈φ) = refl 
subst-id (φ ∨ ψ) p ξ p~∈φ
  rewrite subst-id φ p ξ (aux-left p~∈φ) |
          subst-id ψ p ξ (aux-right (props φ) p~∈φ) = refl 
subst-id (φ ⇒ ψ) p ξ p~∈φ
  rewrite subst-id φ p ξ (aux-left p~∈φ) |
          subst-id ψ p ξ (aux-right (props φ) p~∈φ) = refl 
subst-id (φ ⇔ ψ) p ξ p~∈φ
  rewrite subst-id φ p ξ (aux-left p~∈φ) |
          subst-id ψ p ξ (aux-right (props φ) p~∈φ) = refl 
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:rename-undo)(`rename-undo`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Let `φ : Formula` be a formula and `p q : PropName` two propositions.
Prove that a double substitution ``φ F[ p ↦ ` q ] F[ q ↦ ` p ]`` does not change the formula `φ`
if the variable `q` does not occur in `φ`:

```
rename-undo : ∀ φ p q → q ∉ props φ → φ F[ p ↦ ` q ] F[ q ↦ ` p ] ≡ φ
```

**Warning**: `q ∉ props φ` here is different from `q ~∈ props φ`.
While the latter is just an abbreviation for `~ (q ∈ props φ)`
and thus it provides indirect evidence that `q` is not in `props φ`,
the former provides direct evidence that `q` is not in `props φ`
and thus it is stronger.
The two happen to be equivalent thanks to the coversion functions

```
_ = ~∈→∉ , ∉→~∈
```

*Hint:* Proceed by induction on the evidence `q ∉ props φ` that `q` is not in `φ`.
The following two auxiliary functions will be useful in the inductive cases:

```
_ = ∉-++1 , ∉-++2
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
rename-undo ⊤ p q q∉φ = refl
rename-undo ⊥ p q q∉φ = refl

rename-undo (` r) p q (notThere q≢r _)
  with refl-≡? q
... | q≡?q≡yes
  with p ≡? r
... | yes {refl} rewrite q≡?q≡yes = refl 
... | no
  with q ≡? r
... | yes {refl} = x≢x-elim q≢r
... | no = refl 

rename-undo (¬ φ) p q q∉φ
  rewrite rename-undo φ p q q∉φ = refl

rename-undo (φ ∧ ψ) p q q∉φ
  rewrite rename-undo φ p q (∉-++1 q∉φ) |
          rename-undo ψ p q (∉-++2 {as = props φ} q∉φ)
  = refl
  
rename-undo (φ ∨ ψ) p q q∉φ
  rewrite rename-undo φ p q (∉-++1 q∉φ) |
          rename-undo ψ p q (∉-++2 {as = props φ} q∉φ)
  = refl
  
rename-undo (φ ⇒ ψ) p q q∉φ
  rewrite rename-undo φ p q (∉-++1 q∉φ) |
          rename-undo ψ p q (∉-++2 {as = props φ} q∉φ)
  = refl
  
rename-undo (φ ⇔ ψ) p q q∉φ
  rewrite rename-undo φ p q (∉-++1 q∉φ) |
          rename-undo ψ p q (∉-++2 {as = props φ} q∉φ)
  = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Tautology, entailment, and equivalence

### Tautology

A *tautology* is a formula that evaluates to `tt` under every valuation.

```
Tautology : Formula → Set
Tautology φ = ∀[ ϱ ] ⟦ φ ⟧ ϱ ≡ tt
```

For instance the *law of excluded middle* `` ` p ∨ ¬ ` p ``,
which amounts to say that the propositional variable `p` has either the value `tt` or `ff`,
is a tautology:

```
LEM : Tautology (` p ∨ ¬ ` p)
LEM {p} ϱ with ϱ p
... | tt = refl
... | ff = refl
```

On the other hand, `` ` p `` is not a tautology since the (any) valuation that maps `p` to `ff`
(such as `const ff`) does not satisfy it:

```
_ : ~ Tautology (` p)
_ = λ tau → let ff≡tt = tau (const ff) in ff≢tt ff≡tt
```

Since we can enumerate all valuations `ϱ : Val`
and the equality `⟦ φ ⟧ ϱ ≡ tt` is decidable,
we can *decide* whether `φ` is a tautology:

```
Tautology? : Decidable Tautology
Tautology? φ = ∀?[ ϱ ] ⟦ φ ⟧ ϱ ≡? tt
```

For instance, we can check that `` ` p₀ ∨ ¬ ` p₀ `` is a tautology,
while `` ` p₀ ∨ ` p₁ `` is not by computation,
where `p₀` and `p₁` are two concrete propositions.

```
_ : n ≡ 0 → erase (Tautology? (` p₀ ∨ ¬ ` p₀)) ≡ tt
_ = λ{refl → refl}

_ : n ≡ 0 → erase (Tautology? (` p₀ ∨ ¬ ` p₁)) ≡ ff
_ = λ{refl → refl}
```

(Note that we need to assume that `n` is some concrete number here,
allowing us to actually enumerate all valuations.
We added the function `erase` to convert `yes`, resp., `no`, to `tt`, resp., `ff`,
thus discarding the proof of correctness returned by `Tautology?`.)

### Entailment and equivalence

We say that a formula `φ` *entails* (or *logically implies*) a formula `ψ`,
written `φ ⇛ ψ`, if every valuation that satisfies `φ` satisfies `ψ` as well,
and that they are *logically equivalent*, written `φ ⟺ ψ`,
if they satisfy the same valuations:

```
infix 9 _⇛_ _⟺_

_⇛_ : Formula → Formula → Set
φ ⇛ ψ = ∀[ ϱ ] (⟦ φ ⟧ ϱ ≡ tt → ⟦ ψ ⟧ ϱ ≡ tt)

_⟺_ : Formula → Formula → Set
φ ⟺ ψ =  ∀[ ϱ ] ⟦ φ ⟧ ϱ ≡ ⟦ ψ ⟧ ϱ
```

(Although typographically similar,
entailment `_⇛_` shoud not be confused with the formula implication constructor `_⇒_ : Formula → Formula → Formula`;
the same warning applies to logical equivalence `_⟺_` vs. the bi-implication constructor `_⇔_`.)
For the same reasons as for tautology, entailment and equivalence are decidable:

```
_⇛?_ : ∀ φ ψ → Dec (φ ⇛ ψ)
φ ⇛? ψ = ∀?[ ϱ ] ⟦ φ ⟧ ϱ ≡? tt →? ⟦ ψ ⟧ ϱ ≡? tt

_⟺?_ : ∀ φ ψ → Dec (φ ⟺ ψ)
φ ⟺? ψ = ∀?[ ϱ ] ⟦ φ ⟧ ϱ ≡? ⟦ ψ ⟧ ϱ
```

For instance, we can check that `` ` p₀ `` entails `` ` p₀ ∨ ` p₁ ``, but not `` ` p₁ ``,
and that `` ` p₀ ∧ ` p₁ `` is logically equivalent to `` ` p₁ ∧ ` p₀ ``:

```
_ : n ≡ 0 → erase (` p₀ ⇛? ` p₀ ∨ ` p₁) ≡ tt
_ = λ{refl → refl}

_ : n ≡ 0 → erase (` p₀ ⇛? ` p₁) ≡ ff
_ = λ{refl → refl}

_ : n ≡ 0 → erase (` p₀ ∧ ` p₁ ⟺? ` p₁ ∧ ` p₀) ≡ tt
_ = λ{refl → refl}
```

!exercise(#exercise:entailment-preorder)(Entailment is a preorder)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove that the entailment relation is a preorder:

```
refl-⇛ : ∀ φ → φ ⇛ φ
trans-⇛ : ∀ φ ψ ξ → φ ⇛ ψ → ψ ⇛ ξ → φ ⇛ ξ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
refl-⇛ φ _ = id
trans-⇛ _ _ _ φ⊨ψ ψ⊨ξ ϱ = ψ⊨ξ ϱ ∘ φ⊨ψ ϱ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

For instance, we can prove the double negation law with the method of truth tables:

```
doubleNegationLaw : ∀ φ → ¬ ¬ φ ⟺ φ
doubleNegationLaw φ ϱ with ⟦ φ ⟧ ϱ
... | tt = refl
... | ff = refl
```

!exercise(#exercise:common-equivalences)(Common equivalences)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the folowing equivalences.
*Hint:* Use the method of truth tables.

```
deMorganAnd : ∀ φ ψ → ¬ (φ ∧ ψ) ⟺ ¬ φ ∨ ¬ ψ
deMorganOr : ∀ φ ψ → ¬ (φ ∨ ψ) ⟺ ¬ φ ∧ ¬ ψ
deMorganOr-alt : ∀ φ ψ → φ ∨ ψ ⟺ ¬ (¬ φ ∧ ¬ ψ)
deMorganImplies : ∀ φ ψ → ¬ (φ ⇒ ψ) ⟺ φ ∧ ¬ ψ
deMorganIff : ∀ φ ψ → ¬ (φ ⇔ ψ) ⟺ ¬ φ ⇔ ψ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
deMorganAnd φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

deMorganOr φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

deMorganOr-alt φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

deMorganImplies φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

deMorganIff φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

### Equivalence is a congruence

Logical equivalence is a *congruence*:
Replacing a formula with an equivalent one preserves the semantics.

```
congF : ∀ φ ψ ξ p →
  φ ⟺ ψ →
  -----------------------------
  ξ F[ p ↦ φ ] ⟺ ξ F[ p ↦ ψ ]
```

This is proved with a straightforward structural induction:

```
congF _ _ ⊤ p φ⟺ψ ϱ = refl

congF _ _ ⊥ p φ⟺ψ ϱ = refl

congF _ _ (` q) p φ⟺ψ ϱ
  with p ≡? q
... | yes = φ⟺ψ ϱ
... | no = refl

congF φ ψ (¬ ξ) p φ⟺ψ ϱ
  with congF φ ψ ξ p φ⟺ψ ϱ
... | ind rewrite ind = refl

congF φ ψ (ξ₀ ∧ ξ₁) p φ⟺ψ ϱ
  with congF φ ψ ξ₀ p φ⟺ψ ϱ |
       congF φ ψ ξ₁ p φ⟺ψ ϱ
... | ind₀ | ind₁ rewrite ind₀ | ind₁ = refl

congF φ ψ (ξ₀ ∨ ξ₁) p φ⟺ψ ϱ
  with congF φ ψ ξ₀ p φ⟺ψ ϱ |
       congF φ ψ ξ₁ p φ⟺ψ ϱ
... | ind₀ | ind₁ rewrite ind₀ | ind₁ = refl

congF φ ψ (ξ₀ ⇒ ξ₁) p φ⟺ψ ϱ
  with congF φ ψ ξ₀ p φ⟺ψ ϱ |
       congF φ ψ ξ₁ p φ⟺ψ ϱ
... | ind₀ | ind₁ rewrite ind₀ | ind₁ = refl

congF φ ψ (ξ₀ ⇔ ξ₁) p φ⟺ψ ϱ
  with congF φ ψ ξ₀ p φ⟺ψ ϱ |
       congF φ ψ ξ₁ p φ⟺ψ ϱ
... | ind₀ | ind₁ rewrite ind₀ | ind₁ = refl
```

!exercise(#exercise:cong2F)
~~~~~~~~~~~~~~~~~~~~~~~~~~

Show that replacing *two* formulas with two equivalent ones in parallel respects the semantics:

```
cong2F : ∀ φ₀ φ₁ ψ₀ ψ₁ ξ p₀ p₁ →
  φ₀ ⟺ ψ₀ →
  φ₁ ⟺ ψ₁ →
  -----------------------------------------------------
  ξ F2[ p₀ , p₁ ↦ φ₀ , φ₁ ] ⟺ ξ F2[ p₀ , p₁ ↦ ψ₀ , ψ₁ ]
```
~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~
```
cong2F φ₀ φ₁ ψ₀ ψ₁ ⊥ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ = refl

cong2F φ₀ φ₁ ψ₀ ψ₁ ⊤ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ = refl

cong2F φ₀ φ₁ ψ₀ ψ₁ (` p) p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
  with p₀ ≡? p
... | yes = φ₀⟺ψ₀ ϱ
... | no
  with p₁ ≡? p
... | yes = φ₁⟺ψ₁ ϱ
... | no = refl

cong2F φ₀ φ₁ ψ₀ ψ₁ (¬ ξ) p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
  with cong2F φ₀ φ₁ ψ₀ ψ₁ ξ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
... | ind rewrite ind = refl

cong2F φ₀ φ₁ ψ₀ ψ₁ (ξ₀ ∧ ξ₁) p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
  with cong2F φ₀ φ₁ ψ₀ ψ₁ ξ₀ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ |
       cong2F φ₀ φ₁ ψ₀ ψ₁ ξ₁ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
... | ind₀ | ind₁ rewrite ind₀ | ind₁ = refl

cong2F φ₀ φ₁ ψ₀ ψ₁ (ξ₀ ∨ ξ₁) p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
  with cong2F φ₀ φ₁ ψ₀ ψ₁ ξ₀ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ |
       cong2F φ₀ φ₁ ψ₀ ψ₁ ξ₁ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
... | ind₀ | ind₁ rewrite ind₀ | ind₁ = refl

cong2F φ₀ φ₁ ψ₀ ψ₁ (ξ₀ ⇒ ξ₁) p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
  with cong2F φ₀ φ₁ ψ₀ ψ₁ ξ₀ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ |
       cong2F φ₀ φ₁ ψ₀ ψ₁ ξ₁ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
... | ind₀ | ind₁ rewrite ind₀ | ind₁ = refl

cong2F φ₀ φ₁ ψ₀ ψ₁ (ξ₀ ⇔ ξ₁) p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
  with cong2F φ₀ φ₁ ψ₀ ψ₁ ξ₀ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ |
       cong2F φ₀ φ₁ ψ₀ ψ₁ ξ₁ p₀ p₁ φ₀⟺ψ₀ φ₁⟺ψ₁ ϱ
... | ind₀ | ind₁ rewrite ind₀ | ind₁ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~

## Satisfiability

A formula `φ` is *satisfiable* if there exists some valuation satisfying it:

```
Sat : Formula → Set
Sat φ = ∃[ ϱ ] ⟦ φ ⟧ ϱ ≡ tt
```

Satisfiability is decidable since we can enumerate satisfying assignments:

```
Sat? : ∀ φ → Dec (Sat φ)
Sat? φ = ∃?[ ϱ ] ⟦ φ ⟧ ϱ ≡? tt
```

For instance, the formula `` ` p₀ ∧ ¬ ` p₁ `` is satisfiable,
however `` ` p₀ ∧ ¬ ` p₀ `` is not:

```
_ : n ≡ 0 → erase (Sat? (` p₀ ∧ ¬ ` p₁)) ≡ tt
_ = λ{refl → refl}

_ : n ≡ 0 → erase (Sat? (` p₀ ∧ ¬ ` p₀)) ≡ ff
_ = λ{refl → refl}
```

!exercise(#exercise:tau-sat)(Tautology and satisfiability)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Elaborate and prove a natural property connecting whether `φ` is a tautology and satisfiability.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
tau-sat : ∀ φ → Tautology φ ↔ ~ Sat (¬ φ)
tau-sat φ = tau→sat , sat→tau where

  tau→sat : Tautology φ → ~ Sat (¬ φ)
  tau→sat tauφ (ϱ , ⟦¬φ⟧ϱ≡tt)
    with inspect (⟦ φ ⟧ ϱ)
  ... | it tt ⟦φ⟧ϱ≡tt rewrite ⟦φ⟧ϱ≡tt = ff≢tt ⟦¬φ⟧ϱ≡tt
  ... | it ff ⟦φ⟧ϱ≡ff = ff≢tt (trans (sym ⟦φ⟧ϱ≡ff) (tauφ ϱ))
  
  sat→tau : ~ Sat (¬ φ) → Tautology φ
  sat→tau ~Sat¬φ ϱ
    with inspect (⟦ φ ⟧ ϱ)
  ... | it tt ⟦φ⟧ϱ≡tt = ⟦φ⟧ϱ≡tt
  ... | it ff ⟦φ⟧ϱ≡ff = F-elim (~Sat¬φ (ϱ , ¬𝔹⟦φ⟧ϱ≡tt)) where

    ¬𝔹⟦φ⟧ϱ≡tt : ¬𝔹 ⟦ φ ⟧ ϱ ≡ tt
    ¬𝔹⟦φ⟧ϱ≡tt rewrite ⟦φ⟧ϱ≡ff = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Long conjunctions and disjunctions

### Conjunctions

Sometimes it is useful to interpret a list of formulas as their conjunction.
This is achieved with the following "long conjunction" operation:

```
infix 10 ⋀_
⋀_ : Formula * → Formula
⋀ φs = foldr _∧_ ⊤ φs
```

(Despite the typographical similarity,
`⋀` is a unary function mapping lists of formulas to their logical conjunction,
while `_∧_ : Formula → Formula → Formula` is a binary formula constructor.)
For instance, we have

```
_ : ⋀ [ (` p₀) (` p₁) (` p₂) ] ≡ ` p₀ ∧ ` p₁ ∧ ` p₂ ∧ ⊤
_ = refl
```

The following are the two defining properties of long conjunctions:

```
conjProp1 : ∀ φs ϱ →
  ⟦ ⋀ φs ⟧ ϱ ≡ tt →
  ------------------------
  ∀[ φ ∈ φs ] ⟦ φ ⟧ ϱ ≡ tt

conjProp2 : ∀ φs ϱ →
  ∀[ φ ∈ φs ] ⟦ φ ⟧ ϱ ≡ tt →
  ---------------
  ⟦ ⋀ φs ⟧ ϱ ≡ tt
```

!exercise(#exercise:long-conjunctions)(Long conjunctions)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the two defining properties `conjProp1` and `conjProp2` of long conjunctions
*Hint:* Use the corresponding properties for Booleans.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
conjProp1 _ ϱ ⟦φs⟧≡tt here = 𝔹conjProp1 _ _ ⟦φs⟧≡tt
conjProp1 (ψ ∷ φs) ϱ ⟦ψ∧φs⟧≡tt {φ} (there φ∈φs) = conjProp1 φs ϱ (𝔹conjProp2 (⟦ ψ ⟧ ϱ) _ ⟦ψ∧φs⟧≡tt) φ∈φs

conjProp2 ε ϱ ass = refl
conjProp2 (φ ∷ φs) ϱ ass = 𝔹conjProp3 _ _ ⟦φ⟧ϱ≡tt ⟦⋀φs⟧ϱ≡tt where

  ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
  ⟦φ⟧ϱ≡tt = ass here

  ⟦⋀φs⟧ϱ≡tt : ⟦ ⋀ φs ⟧ ϱ ≡ tt
  ⟦⋀φs⟧ϱ≡tt = conjProp2 φs ϱ λ ψ∈φs → ass (there ψ∈φs)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

### Disjunctions

We can also take "long disjunctions" of a sequence of formulas.
The corresponding two defining properties are dual to those of long conjunctions.

```
infix 9 ⋁_
⋁_ : Formula * → Formula
⋁ φs = foldr _∨_ ⊥ φs

disjProp-tt : ∀ φs ϱ φ →
  φ ∈ φs →
  ⟦ φ ⟧ ϱ ≡ tt →
  ---------------
  ⟦ ⋁ φs ⟧ ϱ ≡ tt

disjProp-ff : ∀ φs ϱ →
  ∀[ φ ∈ φs ] ⟦ φ ⟧ ϱ ≡ ff →
  ---------------
  ⟦ ⋁ φs ⟧ ϱ ≡ ff
```

!exercise(#exercise:long-disjunctions)(Long disjunctions) 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the two defining properties `disjProp-tt` and `disjProp-ff` above.
*Hint:* Use the corresponding properties for Booleans.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
disjProp-tt (φ ∷ _) ϱ φ here ⟦φ⟧ϱ≡tt rewrite ⟦φ⟧ϱ≡tt = refl
disjProp-tt (ψ ∷ _) ϱ φ (there φ∈φs) ⟦φ⟧ϱ≡tt
  with disjProp-tt _ ϱ φ φ∈φs ⟦φ⟧ϱ≡tt
... | ind = 𝔹disjProp2 (⟦ ψ ⟧ ϱ) _ ind

disjProp-ff ε ϱ ass = refl
disjProp-ff (φ ∷ φs) ϱ ass
  with disjProp-ff φs ϱ λ ψ∈φs → ass (there ψ∈φs)
... | ind = 𝔹disjProp3 _ _ (ass here) ind
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Semantic deduction theorem

### Contexts

A *context* is a list of formulas.
The empty context will be denoted by `∅`.

```
Context = Formula *

∅ : Context
∅ = ε
```

If `Γ` is a context and `φ` is a formula,
we can add `φ` to `Γ` and form the new context `Γ · φ`
(this is just adding an element on a list but written on the right).

```
infixl 50 _·_  
_·_ : Context → Formula → Context
Γ · φ = φ ∷ Γ
```

We say that a context `Γ` *entails* (or *logically implies*) a formula `ψ`
if every valuation that satisfies every formula in `Γ`
satisfies `ψ` as well:

```
infix 9 _⊨_
_⊨_ : Context → Formula → Set
Γ ⊨ ψ = ∀ ϱ → All (λ φ → ⟦ φ ⟧ ϱ ≡ tt) Γ → ⟦ ψ ⟧ ϱ ≡ tt
```

!exercise(#exercise:commutative-context)(Commutativity of context)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Show that the order of the formulas in the context does not matter w.r.t. the satisfaction relation:

```
perm-sat : ∀ {Γ Δ ϱ} →
  Perm Γ Δ →
  All (λ φ → ⟦ φ ⟧ ϱ ≡ tt) Γ →
  --------------------------
  All (λ φ → ⟦ φ ⟧ ϱ ≡ tt) Δ
```

*Hint*: Proceed by structural induction on permutations.
Deduce that the logical consequence relation is invariant under context permutation:

```
perm-⊨ : ∀ {Γ Δ} φ →
  Perm Γ Δ →
  Γ ⊨ φ →
  -----
  Δ ⊨ φ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
perm-sat stop AllΓ {φ} φ∈Δ = AllΓ φ∈Δ

perm-sat {ψ ∷ Γ} {ψ ∷ Δ} (skip perm) AllΓ {ψ} here = AllΓ here
perm-sat {ψ ∷ Γ} {ψ ∷ Δ} (skip perm) AllΓ {φ} (there φ∈Δ)
  = perm-sat {Γ} {Δ} perm (λ {ξ} ξ∈Γ → AllΓ (there ξ∈Γ)) φ∈Δ
  
perm-sat (swap perm) AllΓ {_} here = AllΓ (there here)
perm-sat (swap perm) AllΓ {_} (there here) = AllΓ here
perm-sat {φ ∷ ψ ∷ Γ} {ψ ∷ φ ∷ Δ} (swap perm) AllΓ {ξ} (there (there ξ∈Δ))
  = perm-sat perm (AllΓ ∘ there ∘ there) ξ∈Δ 

perm-sat {Γ} {Δ} (tran {bs = Ξ} perm1 perm2) AllΓ
  with perm-sat perm1 AllΓ
... | AllΞ = perm-sat perm2 AllΞ
                            
perm-⊨ φ perm Γ⊨φ ϱ AllΔ = Γ⊨φ ϱ (perm-sat (perm-sym perm) AllΔ)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:context-alt)(Alternative definition of entailment)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
An alternative definition of entailment `Γ ⊨ φ` between a context and a formula
could be based on the previous definition of entailment `ψ ⇛ φ` between two formulas:

```
_⊨′_ : Context → Formula → Set
Γ ⊨′ φ = ⋀ Γ ⇛ φ
```

Show that the two notions of entailment are equivalent:

```
context1 : ∀ {Γ} φ →
  Γ ⊨ φ →
  ------
  Γ ⊨′ φ
  
context2 : ∀ Γ {φ} →
  Γ ⊨′ φ →
  -----
  Γ ⊨ φ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
context1 {Γ} φ Γ⊨φ ϱ ⟦⋀Γ⟧ϱ≡tt = Γ⊨φ ϱ (conjProp1 Γ ϱ ⟦⋀Γ⟧ϱ≡tt)
context2 Γ {φ} ⋀Γ⇛φ ϱ AllΓ = ⋀Γ⇛φ ϱ (conjProp2 Γ ϱ AllΓ)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

### Deduction theorem

The semantic deduction theorem establishes a close connection between the implication connective `_⇒_`,
which is a syntactic object,
and entailment `_⊨_`, which is a semantic one.
It consists of two halves.
The first half shows how to move a formula from the context to the right of `_⊨_`:

```
semDT1 : ∀ Γ φ ψ →
  Γ · φ ⊨ ψ →
  ----------
  Γ ⊨ φ ⇒ ψ
```

The second half shows the converse operation:

```
semDT2 : ∀ Γ φ ψ →
  Γ ⊨ φ ⇒ ψ →
  ---------
  Γ · φ ⊨ ψ
```

!exercise(#exercise:sem-DT)(Semantic deduction theorem)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the two parts `semDT1` and `semDT2` of the semantic deduction theorem.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
semDT1 Γ ψ φ Γ·ψ⊨φ = Δ⊨ψ⇒φ where

  Δ⊨ψ⇒φ : Γ ⊨ ψ ⇒ φ
  Δ⊨ψ⇒φ ϱ ⟦Γ⟧ with inspect (⟦ ψ ⟧ ϱ)
  ... | it ff ⟦ψ⟧ϱ≡ff = 𝔹implProp1 _ _ ⟦ψ⟧ϱ≡ff
  ... | it tt ⟦ψ⟧ϱ≡tt rewrite ⟦ψ⟧ϱ≡tt = trans eql ⟦φ⟧ϱ≡tt where

    eql : tt ⇒𝔹 ⟦ φ ⟧ ϱ ≡ ⟦ φ ⟧ ϱ
    eql = 𝔹implProp2 _ _ refl
    
    ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
    ⟦φ⟧ϱ≡tt = Γ·ψ⊨φ ϱ ⟦ψ∷Γ⟧ where

      ⟦ψ∷Γ⟧ : ∀[ ξ ∈ ψ ∷ Γ ] ⟦ ξ ⟧ ϱ ≡ tt
      ⟦ψ∷Γ⟧ here = ⟦ψ⟧ϱ≡tt
      ⟦ψ∷Γ⟧ (there ξ∈Γ) = ⟦Γ⟧ ξ∈Γ

semDT2 Γ φ ψ Γ⊨φ⇒ψ ϱ AllΓ·φ = ⟦ψ⟧ϱ≡tt where

  AllΓ : All (λ φ → ⟦ φ ⟧ ϱ ≡ tt) Γ
  AllΓ {φ} φ∈Γ = AllΓ·φ (there φ∈Γ)

  ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
  ⟦φ⟧ϱ≡tt = AllΓ·φ here
  
  ⟦ψ⟧ϱ≡tt : ⟦ ψ ⟧ ϱ ≡ tt
  ⟦ψ⟧ϱ≡tt rewrite sym (𝔹implProp2 _ (⟦ ψ ⟧ ϱ) ⟦φ⟧ϱ≡tt) = Γ⊨φ⇒ψ ϱ AllΓ 
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

By repeated application of the semantic deduction theorem,
we can in fact move all formulas from one side to the other.
First, we define "long implications":

```
infix 10 _Imply_
_Imply_ : Formula * → Formula → Formula
ε Imply φ = φ
(ψ ∷ Δ) Imply φ = Δ Imply (ψ ⇒ φ)
```

For instance,

```
_ : ∅ · φ₀ · φ₁ Imply ` p₀ ≡ φ₀ ⇒ φ₁ ⇒ ` p₀
_ = refl
```

We can now state and prove the following "long" versions of the semantic deduction theorem.

```
longSemDT1 : ∀ Δ φ →
  Δ ⊨ φ →
  -------------
  ∅ ⊨ Δ Imply φ
  
longSemDT1 ε φ ε⊨φ = ε⊨φ
longSemDT1 (ψ ∷ Δ) φ ψ∷Δ⊨φ = longSemDT1 Δ (ψ ⇒ φ) (semDT1 Δ ψ φ ψ∷Δ⊨φ)

longSemDT2 : ∀ Δ φ →
  ∅ ⊨ Δ Imply φ →
  -----
  Δ ⊨ φ
  
longSemDT2 ε φ ∅⊨φ ϱ All∅ = ∅⊨φ ϱ All∅
longSemDT2 (ψ ∷ Δ) φ ∅⊨ΔImplyφ = semDT2 Δ ψ φ (longSemDT2 Δ (ψ ⇒ φ) ∅⊨ΔImplyφ)
```

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

# Characteristic formulas {#characteristic-formulas}

Let `ϱ` be a valuation and `φ` a formula.
We say that `φ` is a *characteristic formula* for `ϱ`,
written `φ CharFormulaOf ϱ` if

1) `ϱ` satisfies `φ`, and
2)  no other valuation satisfies `φ`.

Formally, we have the following definition:

```
_CharFormulaOf_ : Formula → Val → Set
φ CharFormulaOf ϱ = ⟦ φ ⟧ ϱ ≡ tt × ∀ ϱ′ → ⟦ φ ⟧ ϱ′ ≡ tt → ϱ′ ≡ ϱ
```

!example(#example:characteristic-formula)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For instance, consider the valuation

```
ϱ₁ = const tt [ p₀ ↦ ff ] [ p₁ ↦ ff ]
```

that assigns value `tt` to every proposition,
except for `p₀` and `p₁`.
Under the assumption that there are only three propositions `p₀, p₁, p₂` in the universe,
a characteristic formula for `ϱ₁` is, e.g.,

```
ψ₁ = ¬ ` p₀ ∧ ¬ ` p₁ ∧ ` p₂
```

In order to show `ψ₁ CharFormulaOf ϱ₁`, we use appropriate Boolean inversion properties
to enforce that every valuation `ϱ′` satisfying `ψ₁`
necessarily assigns `ff` to `p₀, p₁`, and `tt` to `p₂`.
We then use function extensionality to conclude `ϱ′ ≡ ϱ₁`, as required:

```
ψ₁CharFormulaOfϱ₁ : n ≡ 0 → ψ₁ CharFormulaOf ϱ₁
ψ₁CharFormulaOfϱ₁ refl = refl , goal where

  goal : ∀ ϱ′ → ⟦ ψ₁ ⟧ ϱ′ ≡ tt → ϱ′ ≡ ϱ₁
  goal ϱ′ eval
    with 𝔹conjProp1 (⟦ ¬ ` p₀ ⟧ ϱ′) _ eval |
         𝔹conjProp1 (⟦ ¬ ` p₁ ⟧ ϱ′) _ (𝔹conjProp2 (⟦ ¬ ` p₀ ⟧ ϱ′) _ eval) |
         𝔹conjProp2 (⟦ ¬ ` p₁ ⟧ ϱ′) _ (𝔹conjProp2 (⟦ ¬ ` p₀ ⟧ ϱ′) _ eval)
  ... | eval1 | eval2 | eval3
    with ¬𝔹-inv _ eval1 |
         ¬𝔹-inv _ eval2
  ... | eval1' | eval2' = extensionality go where

    go : ∀[ p ] ϱ′ p ≡ ϱ₁ p
    go fzero rewrite eval1' = refl
    go (fsuc fzero) rewrite eval2' = refl
    go (fsuc (fsuc fzero)) rewrite eval3 = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A characteristic formula puts sufficiently many constraints on its satisfying valuations
as to identify a unique satisfying valuation.
Thus, characteristic formulas, which are a syntactic object,
are in bijection with valuations (modulo logical equivalence), which are a semantic object.

!exercise(#exercise:charFormulaUnique)(Uniqueness of characteristic formulas)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove that characteristic formulas of a given valuation are unique,
up to logical equivalence:

```
charFormulaUnique : ∀ φ ψ ϱ →
  φ CharFormulaOf ϱ →
  ψ CharFormulaOf ϱ →
  -----
  φ ⇛ ψ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
charFormulaUnique φ ψ ϱ (_ , φCFϱ) (⟦ψ⟧ϱ≡tt , _) ϱ′ ⟦φ⟧ϱ′≡tt = ⟦ψ⟧ϱ′≡tt where

  ϱ′≡ϱ : ϱ′ ≡ ϱ
  ϱ′≡ϱ = φCFϱ ϱ′ ⟦φ⟧ϱ′≡tt

  ⟦ψ⟧ϱ′≡tt : ⟦ ψ ⟧ ϱ′ ≡ tt
  ⟦ψ⟧ϱ′≡tt rewrite ϱ′≡ϱ = ⟦ψ⟧ϱ≡tt
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Now that we have a notion of characteristic formula,
the next question is whether, given a valuation,
we can construct a characteristic formula for it.
This is the content of the rest of this section.

## Literals

We being by considering single propositional variables.
Given a valuation `ϱ`, we transform a propositional variable `p`
into a corresponding *characteristic literal* `「 p 」 ϱ` depending on whether `ϱ p` is true or false:

```
「_」_ : PropName → Val → Formula
「 p 」 ϱ with ϱ p
... | tt = ` p
... | ff = ¬ ` p
```

In the first case (i.e., if `ϱ p` is `tt`)
we say that the characteristic literal of `「 p 」 ϱ` is *positive*,
and in the other case that it is *negative*.
There are two fundamental properties satisfied by `「 p 」 ϱ`.
The first is *soundness*: `「 p 」 ϱ` is satisfied by `ϱ`:

```
charLit-sound : ∀ ϱ p →
  -------------------
  ⟦ 「 p 」 ϱ ⟧ ϱ ≡ tt

charLit-sound ϱ p with inspect (ϱ p)
... | it tt ϱp≡tt rewrite ϱp≡tt | ϱp≡tt = refl
... | it ff ϱp≡ff rewrite ϱp≡ff | ϱp≡ff = refl
```

(Notice that we need to rewrite twice in each case.
For example in the first case we need to rewrite twice accoriding to the same equality `ϱp≡tt : ϱ p ≡ tt`:
The first rewrite transforms `⟦ 「 p 」 ϱ ⟧ ϱ` into ``⟦ ` p ⟧ ϱ``,
and the second rewrite transforms the latter into `tt`, as required.
A single rewrite does not suffice.
For this reason, the simpler solution

    charLit-sound ϱ p with ϱ p
    ... | tt = refl
    ... | it = refl

only achieves the effect of rewriting once and does not work.)
The second fundamental property of `「 p 」 ϱ` is *completeness*:
For every other valuation `ϱ′` which also satisfies `「 p 」 ϱ`,
it must be the case that `ϱ` and `ϱ′` agree on `p`:

```
charLit-complete : ∀ ϱ p ϱ′ →
  ⟦ 「 p 」 ϱ ⟧ ϱ′ ≡ tt →
  ----------
  ϱ′ p ≡ ϱ p
  
charLit-complete ϱ p ϱ′ ⟦「p」ϱ⟧ϱ′≡tt
  with ϱ p
... | tt = ⟦「p」ϱ⟧ϱ′≡tt
... | ff with ϱ′ p
... | tt = sym ⟦「p」ϱ⟧ϱ′≡tt
... | ff = refl
```

!example(#example:char-lit)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For example, we can compute a positive and a negative characteristic literal of `ϱ₀`:

```
_ : 「 p₀ 」 ϱ₀  ≡ ¬ ` p₀
_ = refl

_ : 「 p₂ 」 ϱ₀  ≡ ` p₂
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Formulas

We can now compute the (a) characteristic formula `〔 ϱ 〕` of a valuation `ϱ`.
The idea is to compute the characteristic literal of every proposition
and then to conjoin all those characteristic literals with a long conjunction:

```
〔_〕 : Val → Formula
〔 ϱ 〕 = ⋀ literals module CharFormula where

  literals : Formula *
  literals = map (「_」 ϱ) propNames
```

(Note how we create a local module named `CharFormula` inside the definition of `〔_〕`.
This will allow us to reuse the definition of `literals` when proving the correctness of the construction.)
Incidentally, we note that characteristic formulas are conjunctive formulas,
i.e., the only logical connectives are `∧` and `¬`.

!example(#example:char-lit)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
For example, we can compute the characteristic formula of `ϱ₀`
(automatically, this time):

```
_ : n ≡ 0 → 〔 ϱ₀ 〕 ≡ ¬ ` p₀ ∧ ¬ ` p₁ ∧ ` p₂ ∧ ⊤
_ = λ{refl → refl}
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Like characteristic literals,
also the construction of characteristic formulas must satisfy the properties of soundness and completeness
in order to be considered correct.
Soundness says that the valuation `ϱ` satisfies its own characteristic formula `〔 ϱ 〕`:

```
charFormula-sound : ∀ ϱ →
  ------------------
  ⟦ 〔 ϱ 〕 ⟧ ϱ ≡ tt
  
charFormula-sound ϱ  = conjProp2 literals ϱ go where

  open CharFormula ϱ

  go : ∀[ φ ∈ literals ] ⟦ φ ⟧ ϱ ≡ tt
  go {φ} φ∈literals
    with map-∈-inv (「_」 ϱ) φ∈literals
  ... | p , _ , φ≡「p」ϱ = ⟦φ⟧ϱ≡tt where

    ⟦「p」ϱ⟧ϱ≡tt : ⟦ 「 p 」 ϱ ⟧ ϱ ≡ tt
    ⟦「p」ϱ⟧ϱ≡tt = charLit-sound ϱ p

    ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
    ⟦φ⟧ϱ≡tt rewrite φ≡「p」ϱ | ⟦「p」ϱ⟧ϱ≡tt = refl
```

Notice how we open the local module `CharFormula` in order to use the definition of `literals` from `〔_〕`.
Completeness says that, if any valuation `ϱ′` satisfies the characteristic formula `〔 ϱ 〕` of a valuation `ϱ`,
then `ϱ′ ≡ ϱ`.

```
charFormula-complete : ∀ ϱ ϱ′ →
  ⟦ 〔 ϱ 〕 ⟧ ϱ′ ≡ tt →
  -----------------
  ϱ′ ≡ ϱ
  
charFormula-complete ϱ ϱ′ ⟦φ⟧ϱ′≡tt = extensionality go where

  go : ∀[ p ] ϱ′ p ≡ ϱ p
  go p = charLit-complete ϱ p ϱ′ (conjProp1 literals ϱ′ ⟦φ⟧ϱ′≡tt ∈literals) where

    open CharFormula ϱ

    ∈literals : 「 p 」 ϱ ∈ literals
    ∈literals = map-∈ (「_」 ϱ) (find p)
```

Soundness and completeness taken together ensure that `〔 ϱ 〕` is a characteristic formula of `ϱ`:

!theorem(#theorem:char-formula)(Characteristic formulas)
~~~~~~~~~~
For every valuation `ϱ` there exists a characteristic formula `〔 ϱ 〕` thereof:

```
thCharFormula : ∀ ϱ →
  -----------------------
  〔 ϱ 〕 CharFormulaOf ϱ
  
thCharFormula ϱ = charFormula-sound ϱ , charFormula-complete ϱ
```
~~~~~~~~~~

Characteristic formulas will be instrumental in the next section in order to show that propositional formulas are functionally complete, in the sense that every Boolean function can be represented as the semantics of a propositional formula.

# Functional completeness {#Functional-Completeness}

The type of the semantic function is `⟦_⟧_ : Formula → Val → 𝔹`.
Once we fix a formula `φ`, it becomes `⟦ φ ⟧_ : Val → 𝔹`,
which is the type of a *Boolean function*, i.e.,
a mapping that takes in input a valuation `Val`
and produces a Boolean value `𝔹`:

```
𝔹Fun = Val → 𝔹
```

The question arises whether every Boolean function can be represented as the semantics `⟦ φ ⟧_`
of some propositional formula `φ`.
We will see shortly that this is the case.
We will also be interested to put restrictions on the connectives that we are allowed to use in order to build `φ`.
A set of connectives is *functionally complete*
if any Boolean function can be expressed by a formula using only connectives in the set:

```
FunctionallyComplete : (Fragment : Formula → Set) → Set
FunctionallyComplete Fragment = ∀[ f ] ∃[ φ ] (Fragment φ × ⟦ φ ⟧_ ≡ f)
```

In this section we explore which set of connectives is functionally complete.

## Fragment `{∨, ∧, ¬, ⊤, ⊥}`

We consider the fragment consisting only of conjunction, disjunction, negation, true, and false.
Thus, w.r.t. the full syntax of propositional formulas,
we do not allow either implication `⇒`, or bi-implication `⇔`.
Formally, this fragment is defined as the following inductive datatype:
   
```
data Formula[⊥,⊤,¬,∨,∧] : Formula → Set where
  ⊥ : Formula[⊥,⊤,¬,∨,∧] ⊥
  ⊤ : Formula[⊥,⊤,¬,∨,∧] ⊤
  `_ : ∀ p → Formula[⊥,⊤,¬,∨,∧] (` p)
  ¬_ : ∀ {φ} → Formula[⊥,⊤,¬,∨,∧] φ → Formula[⊥,⊤,¬,∨,∧] (¬ φ)
  _∧_ : ∀ {φ ψ} → Formula[⊥,⊤,¬,∨,∧] φ → Formula[⊥,⊤,¬,∨,∧] ψ → Formula[⊥,⊤,¬,∨,∧] (φ ∧ ψ)
  _∨_ : ∀ {φ ψ} → Formula[⊥,⊤,¬,∨,∧] φ → Formula[⊥,⊤,¬,∨,∧] ψ → Formula[⊥,⊤,¬,∨,∧] (φ ∨ ψ)
```

In the following, fix an arbitrary Boolean function `f : 𝔹Fun`.
We want to build a formula `φ` in the fragment whose semantics equals that of `f`:

```
funCompl[⊥,⊤,¬,∨,∧] : FunctionallyComplete Formula[⊥,⊤,¬,∨,∧]
```

We will achieve this in three steps:

1) We build the formula `φ` corresponding to `f`.
2) We show that `φ` is in the fragment.
3) We show that the formula `φ` is indeed equivalent to `f`.

*Step 1*. The construction of the formula is based on the characteristic formulas from the previous section.
Namely, we consider all valuations `ϱ` s.t. `f ϱ ≡ tt` and we take the disjunction of their characteristic formulas:

```
fun→formula : 𝔹Fun → Formula
fun→formula f = ⋁ φs module 𝔹Fun→Formula where

  ttVals = filter (λ ϱ → f ϱ ≡? tt) vals
  φs = map 〔_〕 ttVals
```

(We give a module name `𝔹Fun→Formula` in the internal declarations of `ttVals` and `φs` above
in order to be able to reuse them later on.

!example(#example-fun2formula)
~~~~~~~~~~~~~~~~~~~~~~~~~
For instance, consider the following Boolean function that returns true iff all its inputs are equal,
and false otherwise:

```
f₀ : 𝔹Fun
f₀ ϱ = foldr (λ b₀ b₁ → b₁ ∧𝔹 erase (b₀ ≡? ϱ p₀)) tt (map ϱ propNames)
```

We can construct the corresponding formula in the special case of three propositional variables
(the application of !ref(simplify) removes some redundant !ref(Formula)(⊤) and !ref(Formula)(⊥) constants):

```
_ : n ≡ 0 → simplify (fun→formula f₀) ≡
  ` p₀ ∧ ` p₁ ∧ ` p₂ ∨
    ¬ ` p₀ ∧ ¬ ` p₁ ∧ ¬ ` p₂
_ = λ{ refl → refl}
```
~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:fun2formula)(The xor function)
~~~~~~~~~~~~~~~~~~~~~~~~~~
Define the Boolean function that computes the exclusive-or (xor) of its inputs
and compute the corresponding formula with the help of `fun→formula`.
~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~
```
xor : 𝔹Fun
xor ϱ = foldr (λ b₀ b₁ → erase (b₀ ≡? b₁)) (ϱ p₀) (tail (map ϱ propNames))

_ : n ≡ 0 → simplify (fun→formula xor) ≡
  ` p₀ ∧ ` p₁ ∧ ` p₂ ∨
    ¬ ` p₀ ∧ ¬ ` p₁ ∧ ` p₂ ∨
      ¬ ` p₀ ∧ ` p₁ ∧ ¬ ` p₂ ∨
        ` p₀ ∧ ¬ ` p₁ ∧ ¬ ` p₂
_ = λ{refl → refl}
```
~~~~~~~~~~~~~~~~~~~~~~~~~~

*Step 2*. In the second step we show that !ref(fun→formula) outputs a formula in the !ref(Formula[⊥,⊤,¬,∨,∧]) fragment.
In fact, it more natural to show the stronger fact that the !ref(Formula[⊥,⊤,¬,∨,∧]) fragment is closed under long conjunctions and disjunctions:

```
Formula[⊥,⊤,¬,∨,∧]-⋀-closed : ∀ φs → All Formula[⊥,⊤,¬,∨,∧] φs → Formula[⊥,⊤,¬,∨,∧] (⋀ φs)
Formula[⊥,⊤,¬,∨,∧]-⋀-closed ε all = ⊤
Formula[⊥,⊤,¬,∨,∧]-⋀-closed (φ ∷ φs) all
  with Formula[⊥,⊤,¬,∨,∧]-⋀-closed φs (λ φ∈φs → all (there φ∈φs))
... | ind = all here ∧ ind

Formula[⊥,⊤,¬,∨,∧]-⋁-closed : ∀ φs → All Formula[⊥,⊤,¬,∨,∧] φs → Formula[⊥,⊤,¬,∨,∧] (⋁ φs)
Formula[⊥,⊤,¬,∨,∧]-⋁-closed ε all = ⊥
Formula[⊥,⊤,¬,∨,∧]-⋁-closed (φ ∷ φs) all
  with Formula[⊥,⊤,¬,∨,∧]-⋁-closed φs (λ φ∈φs → all (there φ∈φs))
... | ind = all here ∨ ind
```

Characteristic literals obviously are in the fragment:

```
charLit-fragment : ∀ ϱ p → Formula[⊥,⊤,¬,∨,∧] (「 p 」 ϱ )
charLit-fragment ϱ p with ϱ p
... | tt = ` p
... | ff = ¬ ` p
```

Characteristic formulas are in the fragment,
thanks to closure under long conjunctions:

```
charFormula-fragment : ∀ ϱ → Formula[⊥,⊤,¬,∨,∧] 〔 ϱ 〕
charFormula-fragment ϱ = Formula[⊥,⊤,¬,∨,∧]-⋀-closed literals all where

  open CharFormula ϱ

  all : All Formula[⊥,⊤,¬,∨,∧] literals
  all φ∈literals
    with map-∈-inv _ φ∈literals
  ... | p , _ , φ≡「p」ϱ rewrite φ≡「p」ϱ = charLit-fragment ϱ p
```

Finally, also `fun→formula f` is in the fragment,
thanks to closure under long disjunctions:

```
∈fragment : ∀ f → Formula[⊥,⊤,¬,∨,∧] (fun→formula f)
∈fragment f = Formula[⊥,⊤,¬,∨,∧]-⋁-closed φs all where

  open 𝔹Fun→Formula f

  all : All Formula[⊥,⊤,¬,∨,∧] φs
  all ψ∈φs
    with map-∈-inv _ ψ∈φs
  ... | ϱ , _ , ψ≡〔ϱ〕 rewrite ψ≡〔ϱ〕 = charFormula-fragment ϱ
```

*Step 3*. In the last step, we show that !ref(fun→formula) produces a formula which is equivalent to the input Boolean function.
The proof is based on both soundness and completeness of characteristic formulas `〔 ϱ 〕`.

```
fun→formula-correct : ∀ f → ∀[ ϱ ] ⟦ fun→formula f ⟧ ϱ ≡ f ϱ
fun→formula-correct f ϱ with inspect (f ϱ)
```

We perform a case analysis on `f ϱ`.
If `f` evaluates to true on `ϱ`,
then we need to show that `fun→formula f` also evaluates to true:

```
... | it tt fϱ≡tt rewrite fϱ≡tt = goal where

  open 𝔹Fun→Formula f

  goal : ⟦ fun→formula f ⟧ ϱ ≡ tt
```

We begin by finding the occurrence `findVal ϱ` of `ϱ` in the list of all valuations !ref(vals) and then, knowing that `f ϱ` evaluates to `tt` by assumption,
we find a witness `ϱ∈ttVals` that `ϱ` belongs to !ref(𝔹Fun→Formula)(ttVals):

```
  goal
    with filter-∈ (findVal ϱ) fϱ≡tt
  ... | ϱ∈ttVals
```

Thus, by the definition of !ref(𝔹Fun→Formula)(φs),
we have `〔 ϱ 〕 ∈ φs`:

```
    with map-∈ _ ϱ∈ttVals
  ... | 〔ϱ〕∈φs
```

By soundness of characteristic formulas,
we have `⟦ 〔 ϱ 〕 ⟧ ϱ ≡ tt`:

```
    with charFormula-sound ϱ
  ... | ⟦〔ϱ〕⟧ϱ≡tt = disjProp-tt φs ϱ 〔 ϱ 〕 〔ϱ〕∈φs ⟦〔ϱ〕⟧ϱ≡tt
```

The proof ends by !ref(disjProp-tt) since we found a disjunct `〔 ϱ 〕` that evaluates to true.

In the second case, `f` evaluates to false on `ϱ`,
and thus we must show the same for `fun→formula f `.
In order to achieve this, we use again the disjunction property,
which requires us to prove that all disjuncts in !ref(𝔹Fun→Formula)(φs) evaluate to false:

```
... | it ff fϱ≡ff rewrite fϱ≡ff = disjProp-ff φs ϱ goal where

  open 𝔹Fun→Formula f
  
  goal : ∀[ φ ∈ φs ] ⟦ φ ⟧ ϱ ≡ ff
```

We thus consider an arbitrary `φ` in !ref(𝔹Fun→Formula)(φs) and do a case analysis on its value under `ϱ`.
If it evaluates to false, then we are done:

```
  goal {φ} φ∈φs
    with inspect (⟦ φ ⟧ ϱ)
  ... | it ff ⟦φ⟧ϱ≡ff = ⟦φ⟧ϱ≡ff
```

Otherwise, `φ` evaluates to true, and we look for a contradiction.
First of all, since `φ` is a disjunct in !ref(𝔹Fun→Formula)(φs),
by definition it is the characteristic formula of some valuation `ϱ′` in !ref(𝔹Fun→Formula)(ttVals):

```
  ... | it tt ⟦φ⟧ϱ≡tt
    with map-∈-inv 〔_〕 φ∈φs
  ... | ϱ′ , ϱ′∈ttVals , φ≡〔ϱ′〕 
```

By definition, !ref(𝔹Fun→Formula)(ttVals) is the list of those valuations `ϱ` s.t. `f ϱ` is true.
Since `ϱ′` is one of those, `f ϱ′` must be true:

```
    with filter-∈-inv vals ϱ′∈ttVals 
  ... | ϱ′∈vals , fϱ′≡tt
```

We would like to deduce that `ϱ` is equal to `ϱ′` by completeness of characteristic formulas.
In order to apply !ref(〔 〕-complete), we need to show `⟦ 〔 ϱ′ 〕 ⟧ ϱ ≡ tt`.
But this is certainly true, since `⟦ φ ⟧ ϱ ≡ tt` by assumption,
and `φ ≡ 〔 ϱ′ 〕` by the definition of `ϱ′`:

```
    rewrite φ≡〔ϱ′〕
    with charFormula-complete ϱ′ ϱ ⟦φ⟧ϱ≡tt
  ... | ϱ≡ϱ′
```

We can now reach the sought contradiction since `f ϱ′ ≡ tt` and `f ϱ ≡ ff` at the same time:

```
    rewrite ϱ≡ϱ′ = a≡ff→a≡tt-elim fϱ≡ff fϱ′≡tt
```

This concludes the second and last  case of the correctness proof.
We can put all the pieces together and show that the fragment is functionally complete.

!theorem(#theorem:funComplFalseTrueNegAndOr)(Functional completeness of `{∨, ∧, ¬, ⊤, ⊥}`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
funCompl[⊥,⊤,¬,∨,∧] f =
  fun→formula f , ∈fragment f , extensionality (fun→formula-correct f)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Fragment `{∨, ∧, ¬}`

Let's restrict our previous fragment !ref(Formula[⊥,⊤,¬,∨,∧]) by forbidding the constants !ref(Formula)(⊥) and !ref(Formula)(⊤).
Formally, we have the following definition:

```
data Formula[¬∨∧] : Formula → Set where
  `_ : ∀ p → Formula[¬∨∧] (` p)
  ¬_ : ∀ {φ} → Formula[¬∨∧] φ → Formula[¬∨∧] (¬ φ)
  _∧_ : ∀ {φ ψ} → Formula[¬∨∧] φ → Formula[¬∨∧] ψ → Formula[¬∨∧] (φ ∧ ψ)
  _∨_ : ∀ {φ ψ} → Formula[¬∨∧] φ → Formula[¬∨∧] ψ → Formula[¬∨∧] (φ ∨ ψ)
```

We show that this fragment is functionally complete:

```
funCompl[¬∨∧] : FunctionallyComplete Formula[¬∨∧]
```

Thanks to the fact that !ref(Formula[⊥,⊤,¬,∨,∧]) is functionally complete (c.f. !ref(funCompl[⊥,⊤,¬,∨,∧]))
it suffices to remove the two logical constants `⊥` and `⊤`:

```
remove⊥⊤ : ∀ {φ} →
  Formula[⊥,⊤,¬,∨,∧] φ →
  -------------------------------
  ∃[ ψ ] Formula[¬∨∧] ψ × φ ⟺ ψ
```

In order to do so, we need to have at least one propositional variable `p₀` at our disposal
(which is indeed the case).
We replace `⊥` with `` ` p₀ ∧ ¬ ` p₀``
and `⊤` with `` ` p₀ ∨ ¬ ` p₀``,
using the fact that we have at least one proposition `p₀`:

```
remove⊥⊤ {⊥} ⊥ = _ , ` p₀ ∧ ¬ ` p₀ , ⊥⟺p₀∧¬p₀ where

  ⊥⟺p₀∧¬p₀ : ⊥ ⟺ ` p₀ ∧ ¬ ` p₀
  ⊥⟺p₀∧¬p₀ ϱ with ϱ p₀
  ... | tt = refl
  ... | ff = refl

remove⊥⊤ {⊤} ⊤ = _ , ` p₀ ∨ ¬ ` p₀ , ⊤⟺p₀∨¬p₀ where

  ⊤⟺p₀∨¬p₀ : ⊤ ⟺ ` p₀ ∨ ¬ ` p₀
  ⊤⟺p₀∨¬p₀ ϱ with ϱ p₀
  ... | tt = refl
  ... | ff = refl
```

The variable case is straightforward:

```
remove⊥⊤ {` p} (` p) = ` p , ` p , λ ϱ → refl
```

The inductive cases are also rather easy.
We recursively compute the inductive assumption
and then we use the two congruence lemmas !ref(congF) and !ref(cong2F) in order to show correctness:

```
remove⊥⊤ {¬ φ} (¬ F[⊥,⊤,¬,∨,∧]φ)
  with remove⊥⊤ F[⊥,⊤,¬,∨,∧]φ
... | ψ , F[¬∨∧]ψ , φ⟺ψ = ¬ ψ , ¬ F[¬∨∧]ψ , congF φ ψ (¬ ` p₀) p₀ φ⟺ψ

remove⊥⊤ {φ ∧ ψ} (F[⊥,⊤,¬,∨,∧]φ ∧ F[⊥,⊤,¬,∨,∧]ψ)
  with remove⊥⊤ {φ} F[⊥,⊤,¬,∨,∧]φ |
       remove⊥⊤ {ψ} F[⊥,⊤,¬,∨,∧]ψ
... | φ′ , F[¬∨∧]φ′ , φ⟺φ′
    | ψ′ , F[¬∨∧]ψ′ , ψ⟺ψ′ =
      φ′ ∧ ψ′ , F[¬∨∧]φ′ ∧ F[¬∨∧]ψ′ , cong2F φ ψ φ′ ψ′ (` p₀ ∧ ` p₁) p₀ p₁ φ⟺φ′ ψ⟺ψ′ 

remove⊥⊤ {φ ∨ ψ} (F[⊥,⊤,¬,∨,∧]φ ∨ F[⊥,⊤,¬,∨,∧]ψ)
  with remove⊥⊤ {φ} F[⊥,⊤,¬,∨,∧]φ |
       remove⊥⊤ {ψ} F[⊥,⊤,¬,∨,∧]ψ
... | φ′ , F[¬∨∧]φ′ , φ⟺φ′
    | ψ′ , F[¬∨∧]ψ′ , ψ⟺ψ′ =
      φ′ ∨ ψ′ , F[¬∨∧]φ′ ∨ F[¬∨∧]ψ′ , cong2F φ ψ φ′ ψ′ (` p₀ ∨ ` p₁) p₀ p₁ φ⟺φ′ ψ⟺ψ′ 
```

With !ref(remove⊥⊤) in hand, it is easy to prove functional completeness of this fragment:

```
funCompl[¬∨∧] f
  with funCompl[⊥,⊤,¬,∨,∧] f
... | φ , Formula[⊥,⊤,¬,∨,∧]φ , ⟦φ⟧≡f
  with remove⊥⊤ Formula[⊥,⊤,¬,∨,∧]φ
... | ψ , Formula[¬∨∧]ψ , φ⟺ψ rewrite sym ⟦φ⟧≡f
  = ψ , Formula[¬∨∧]ψ , sym (extensionality φ⟺ψ) 
```

!exercise(#exercise:removeTrueFalse-alt)
~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have seen that one way to remove the constants !ref(Formula)(⊤) and !ref(Formula)(⊥) is to convert them "locally" to simple tautologies, resp., absurdities, involving a fixed propositional variable.
This style of solution will be useful in !refSection(#sec:FragmentsAndNeg).
Are there alternative ways to achieve the same effect?
~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Certainly there are. One possibility is to repeatedly apply !ref(simplify) until no more constants appear in the formula.
The tricky part is to encode this in such a way as to convince the termination checker.
Note that each application of !ref(simplify) either leaves the formula unaltered
or it strictly decreases its size.
Based on this observation, one could define a repeated application of !ref(simplify) by well-founded recursion on the size of formulas.
We omit the details here, but we will see definitions by well-founded recursion in the [NormalForms](/part1/NormalForms/) chapter.
~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Fragments `{∧, ¬}` and `{∨, ¬}` {#sec:FragmentsAndNeg}

We further restrict the syntax by additionally forbidding disjunction `∨`:

```
data Formula[¬∧] : Formula → Set where
  `_ : ∀ p → Formula[¬∧] (` p)
  ¬_ : ∀ {φ} → Formula[¬∧] φ → Formula[¬∧] (¬ φ)
  _∧_ : ∀ {φ ψ} → Formula[¬∧] φ → Formula[¬∧] ψ → Formula[¬∧] (φ ∧ ψ)
```

Since the fragments `{∧, ¬}` and `{∨, ¬}` are dual to each other,
we focus on the former.

!exercise(#exercise:FormulaNegAnd)(Functional completeness of `{∧, ¬}`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Show that !ref(Formula[¬∧]) is functionally complete:

```
funCompl[¬∧] : FunctionallyComplete Formula[¬∧]
```

*Hint*: Use functional completeness of !ref(Formula[¬∨∧]), as proved in !ref(funCompl[¬∨∧]),
and use de Morgan's law to express disjunction `∨` in terms of conjunction `∧` and negation `¬`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~
We start with an auxiliary procedure doing the heavy lifting of removing disjunction:

```
remove∨ : ∀ {φ} →
  Formula[¬∨∧] φ →
  ------------------------------
  ∃[ ψ ] Formula[¬∧] ψ × φ ⟺ ψ
```

The variable case, negation, and conjunction are straightforward:

```
remove∨ {` p} (` p) = ` p , ` p , λ ϱ → refl

remove∨ {¬ φ} (¬ F[¬∨∧]φ)
  with remove∨ F[¬∨∧]φ
... | ψ , F[¬∧]ψ , φ⟺ψ = ¬ ψ , ¬ F[¬∧]ψ , congF φ ψ (¬ ` p₀) p₀ φ⟺ψ

remove∨ {φ ∧ ψ} (F[¬∨∧]φ ∧ F[¬∨∧]ψ)
  with remove∨ {φ} F[¬∨∧]φ |
       remove∨ {ψ} F[¬∨∧]ψ
... | φ′ , F[¬∧]φ′ , φ⟺φ′
    | ψ′ , F[¬∧]ψ′ , ψ⟺ψ′ =
      φ′ ∧ ψ′ , F[¬∧]φ′ ∧ F[¬∧]ψ′ , cong2F φ ψ φ′ ψ′ (` p₀ ∧ ` p₁) p₀ p₁ φ⟺φ′ ψ⟺ψ′ 
```

The only non-trivial case is the one for disjunction.
Here, we remove it thanks to de Morgan's law:

```
remove∨ {φ ∨ ψ} (F[¬∨∧]φ ∨ F[¬∨∧]ψ)
  with remove∨ {φ} F[¬∨∧]φ |
       remove∨ {ψ} F[¬∨∧]ψ
... | φ′ , F[¬∧]φ′ , φ⟺φ′
    | ψ′ , F[¬∧]ψ′ , ψ⟺ψ′ =
      ¬ (¬ φ′ ∧ ¬ ψ′) , ¬ (¬ F[¬∧]φ′ ∧ ¬ F[¬∧]ψ′) , goal where

    goal : ∀[ ϱ ] ⟦ φ ∨ ψ ⟧ ϱ ≡ ⟦ ¬ (¬ φ′ ∧ ¬ ψ′) ⟧ ϱ
    goal ϱ rewrite φ⟺φ′ ϱ | ψ⟺ψ′ ϱ = deMorganOr-alt φ′ ψ′ ϱ
```

With !ref(remove∨) in hand, it is immediate to conclude the proof of functional completeness:

```
funCompl[¬∧] f
  with funCompl[¬∨∧] f
... | φ , Formula[¬∨∧]φ , ⟦φ⟧≡f
  with remove∨ {φ} Formula[¬∨∧]φ
... | ψ , Formula[¬∧]ψ , φ⟺ψ rewrite ⟦φ⟧≡f
  = ψ , Formula[¬∧]ψ , sym (extensionality φ⟺ψ)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Fragment `{⇒, ⊥}`

We now consider yet another fragment, where we only allow implication and the false constant:

```
data Formula[⇒,⊥] : Formula → Set where
  ⊥ : Formula[⇒,⊥] ⊥
  `_ : ∀ p → Formula[⇒,⊥] (` p)
  _⇒_ : ∀ {φ ψ} → Formula[⇒,⊥] φ → Formula[⇒,⊥] ψ → Formula[⇒,⊥] (φ ⇒ ψ)
```

!exercise(#exercise:FormulaImplFalse)(Functional completeness of `{⇒, ⊥}`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~
Show that !ref(Formula[⇒,⊥]) is functionally complete:

```
funCompl[⇒,⊥] : FunctionallyComplete Formula[⇒,⊥]
```

*Hint*: Find a way express conjunction and negation in terms of implication `⇒`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
convert[¬,∧]→[⇒,⊥] : ∀ {φ} →
  Formula[¬∧] φ →
  -------------------------------
  ∃[ ψ ] Formula[⇒,⊥] ψ × φ ⟺ ψ

convert[¬,∧]→[⇒,⊥] {` p} (` p) = ` p , ` p , λ ϱ → refl

convert[¬,∧]→[⇒,⊥] {¬ φ} (¬ F[¬∧]φ)
  with convert[¬,∧]→[⇒,⊥] F[¬∧]φ
... | ψ , F[¬∧]ψ , φ⟺ψ =  ψ ⇒ ⊥ , F[¬∧]ψ ⇒ ⊥ , ¬φ⟺ψ⇒⊥ where

  ¬φ⟺ψ⇒⊥ : ¬ φ ⟺ ψ ⇒ ⊥
  ¬φ⟺ψ⇒⊥ ϱ rewrite φ⟺ψ ϱ
    with ⟦ ψ ⟧ ϱ
  ... | tt = refl
  ... | ff = refl

convert[¬,∧]→[⇒,⊥] {φ ∧ ψ} (F[¬∧]φ ∧ F[¬∧]ψ)
  with convert[¬,∧]→[⇒,⊥] {φ} F[¬∧]φ |
       convert[¬,∧]→[⇒,⊥] {ψ} F[¬∧]ψ
... | φ′ , F[¬∧]φ′ , φ⟺φ′
    | ψ′ , F[¬∧]ψ′ , ψ⟺ψ′ =
       (φ′ ⇒ (ψ′ ⇒ ⊥)) ⇒ ⊥ , (F[¬∧]φ′ ⇒ F[¬∧]ψ′ ⇒ ⊥) ⇒ ⊥ , goal where

    goal : φ ∧ ψ ⟺ (φ′ ⇒ ψ′ ⇒ ⊥) ⇒ ⊥
    goal ϱ rewrite φ⟺φ′ ϱ | ψ⟺ψ′ ϱ
      with ⟦ φ′ ⟧ ϱ | ⟦ ψ′ ⟧ ϱ
    ... | tt | tt = refl
    ... | tt | ff = refl
    ... | ff | tt = refl
    ... | ff | ff = refl
```

```
funCompl[⇒,⊥] f
  with funCompl[¬∧] f
... | φ , Formula[¬∧]φ , ⟦φ⟧≡f
  with convert[¬,∧]→[⇒,⊥] {φ} Formula[¬∧]φ
... | ψ , Formula[⇒,⊥]ψ , φ⟺ψ rewrite ⟦φ⟧≡f
  = ψ , Formula[⇒,⊥]ψ , sym (extensionality φ⟺ψ)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Fragment `{⊥, ⊤, ∨, ∧}`

In this section we explore the fragment where we only allow conjunction and disjunction,
i.e., no negation, implication, or bi-implication:

```
data Formula[⊥,⊤,∨,∧] : Formula → Set where
  ⊥ : Formula[⊥,⊤,∨,∧] ⊥
  ⊤ : Formula[⊥,⊤,∨,∧] ⊤
  `_ : ∀ p → Formula[⊥,⊤,∨,∧] (` p)
  _∧_ : ∀ {φ ψ} → Formula[⊥,⊤,∨,∧] φ → Formula[⊥,⊤,∨,∧] ψ → Formula[⊥,⊤,∨,∧] (φ ∧ ψ)
  _∨_ : ∀ {φ ψ} → Formula[⊥,⊤,∨,∧] φ → Formula[⊥,⊤,∨,∧] ψ → Formula[⊥,⊤,∨,∧] (φ ∨ ψ)
```

As a preparation for the following,
we prove that this fragment is closed under long intersections and disjunctions:

```
Formula[⊥,⊤,∨,∧]-⋀-closed : ∀ φs →
  All Formula[⊥,⊤,∨,∧] φs →
  -----------------------
  Formula[⊥,⊤,∨,∧] (⋀ φs)
  
Formula[⊥,⊤,∨,∧]-⋁-closed : ∀ φs →
  All Formula[⊥,⊤,∨,∧] φs →
  -----------------------
  Formula[⊥,⊤,∨,∧] (⋁ φs)
```

<!-- *Hint*: C.f. !ref(Formula[⊥,⊤,¬,∨,∧]-⋀-closed) and !ref(Formula[⊥,⊤,¬,∨,∧]-∨-closed). -->

!hide
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The two proofs are identical to !ref(Formula[⊥,⊤,¬,∨,∧]-⋀-closed), resp., !ref(Formula[⊥,⊤,¬,∨,∧]-∨-closed).
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
Formula[⊥,⊤,∨,∧]-⋀-closed ε all = ⊤
Formula[⊥,⊤,∨,∧]-⋀-closed (φ ∷ φs) all
  with Formula[⊥,⊤,∨,∧]-⋀-closed φs (λ φ∈φs → all (there φ∈φs))
... | ind = all here ∧ ind

Formula[⊥,⊤,∨,∧]-⋁-closed ε all = ⊥
Formula[⊥,⊤,∨,∧]-⋁-closed (φ ∷ φs) all
  with Formula[⊥,⊤,∨,∧]-⋁-closed φs (λ φ∈φs → all (there φ∈φs))
... | ind = all here ∨ ind
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:fragmentAndOr)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Is this fragment semantically complete?
Find a Boolean function which cannot be expressed in the fragment.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
This fragment is not complete w.r.t. all Boolean functions.
For example, the negation function (say of the first variable) cannot be expressed:

```
f¬ : 𝔹Fun
f¬ ϱ = ¬𝔹 ϱ p₀
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The first observation is that this fragment can only encode monotone Boolean functions.
(We have here in mind the natural ordering `ff ≤𝔹 tt` on `𝔹`.)
Intuitively, a Boolean function is monotone iff flipping one input from `ff` to `tt` can only increase the output.
Formally, we define a partial order `_≤V_` on valuation by lifting `_≤𝔹_` point-wise in the expected way:

```
_≤V_ : Val → Val → Set
ϱ ≤V ϱ′ = ∀[ p ] ϱ p ≤𝔹 ϱ′ p
```

which allows us to define what it means for a Boolean function to be monotone:

```
Monotone : 𝔹Fun → Set
Monotone f = ∀ ϱ ϱ′ → ϱ ≤V ϱ′ → f ϱ ≤𝔹 f ϱ′
```

!exercise(#exercise:negNotMonotone)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Formally Prove that the counterexample you constructed in !refExercise(#exercise:fragmentAndOr) is not monotone.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Our counterexample !ref(f¬) is not monotone:

```
f¬-notMonotone : ~ Monotone f¬
f¬-notMonotone mon = ~tt≤𝔹ff tt≤ff where

  ϱff ϱtt : Val
  ϱff = const ff
  ϱtt = const tt

  ϱff≤ϱtt : ϱff ≤V ϱtt
  ϱff≤ϱtt p = ff≤tt

  tt≤ff : tt ≤𝔹 ff
  tt≤ff = mon ϱff ϱtt ϱff≤ϱtt
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:fragmentAndOrOnlyMonotone)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove that the `{⊥, ⊤, ∨, ∧}` fragment can only represent monotone functions:

```
only-monotone : ∀ {φ} → Formula[⊥,⊤,∨,∧] φ → Monotone ⟦ φ ⟧_
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The proof follows a straightforward structural induction.
The two constants case is immediate:

```
only-monotone ⊥ _ _ _ = ff≤ff
only-monotone ⊤ _ _ _ = tt≤tt
```

In the variable case, we use the monotonicity assumption:

```
only-monotone (` p) α β α≤β = α≤β p
```

In the two inductive cases,
we use the monotonicity of the semantics of conjunction and disjunction:

```
only-monotone (viewφ ∧ viewψ) α β α≤β with
  only-monotone viewφ α β α≤β |
  only-monotone viewψ α β α≤β
... | ⟦φ⟧α≤⟦φ⟧β | ⟦ψ⟧α≤⟦ψ⟧β = monotone-∧𝔹 ⟦φ⟧α≤⟦φ⟧β ⟦ψ⟧α≤⟦ψ⟧β

only-monotone (viewφ ∨ viewψ) α β α≤β with
  only-monotone viewφ α β α≤β |
  only-monotone viewψ α β α≤β
... | ⟦φ⟧α≤⟦φ⟧β | ⟦ψ⟧α≤⟦ψ⟧β = monotone-∨𝔹 ⟦φ⟧α≤⟦φ⟧β ⟦ψ⟧α≤⟦ψ⟧β
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This suggests that the `{⊥, ⊤, ∨, ∧}` fragment may be able to encode *all* monotone Boolean functions.
This is true and slightly harder to prove.

We begin by encoding of the single literals:

```
monCharLit : Val → PropName → Formula
monCharLit ϱ p
  with ϱ p
... | tt = ` p
... | ff = ⊤ -- !
```

The second case of the definition above may be surprising
since we are just ignoring the proposition `p` when the valuation `ϱ` says false.
Monotonicity will ensure that this is the right definition.

!exercise(#exercise:monCharLit-Formula)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Formally prove that !ref(monCharLit) produces a formula in the fragment:

```
monCharLit-Formula[⊥,⊤,∨,∧] : ∀ ϱ p →
  ---------------------------------
  Formula[⊥,⊤,∨,∧] (monCharLit ϱ p)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
monCharLit-Formula[⊥,⊤,∨,∧] ϱ p
  with ϱ p
... | tt = ` p
... | ff = ⊤
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:monCharLit-sound-complete)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove that !ref(monCharLit) is sound and complete in the following sense:

```
monCharLit-soundness : ∀ ϱ p →
  -----------------------
  ⟦ monCharLit ϱ p ⟧ ϱ ≡ tt

monCharLit-completeness : ∀ ϱ p ϱ′ →
  ⟦ monCharLit ϱ p ⟧ ϱ′ ≡ tt →
  ------------
  ϱ p ≤𝔹 ϱ′ p
```

Notice that we just require the more relaxed `ϱ p ≤𝔹 ϱ′ p` in !ref(monCharLit-completeness),
instead of a full equality `ϱ p ≡ ϱ′ p` as in !ref(charLit-completeness).
This is the correct choice since we will only be representing monotone Boolean functions.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
monCharLit-soundness ϱ p
  with inspect (ϱ p)
... | it tt eq rewrite eq | eq = refl 
... | it ff eq rewrite eq = refl
            
monCharLit-completeness ϱ p ϱ′ ⟦φ⟧ϱ′≡tt
    with inspect (ϱ p) | inspect (ϱ′ p)
... | it tt eq | it tt eq′ rewrite ⟦φ⟧ϱ′≡tt | eq | eq′ = tt≤tt
... | it ff eq | it tt eq′ rewrite ⟦φ⟧ϱ′≡tt | eq | eq′ = ff≤tt
... | it tt eq | it ff eq′ rewrite ⟦φ⟧ϱ′≡tt | eq | eq′ = ff≢tt-elim ⟦φ⟧ϱ′≡tt
... | it ff eq | it ff eq′ rewrite ⟦φ⟧ϱ′≡tt | eq | eq′ = ff≤ff
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We now build monotone characteristic formulas,
following the same idea as in !ref(〔_〕)—but of course replacing !ref(「_」_) with !ref(monCharLit):

```
monCharFormula : Val → Formula
monCharFormula ϱ = ⋀ map (monCharLit ϱ) propNames
```

!exercise(#exercise-monCharFormula)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Show that

1) monotone characteristic formulas belong to the fragment, c.f. !ref(charFormula-Formula[⊥,⊤,¬,∨,∧]),
2) they are sound, and
3) they are complete:

```
monCharFormula-Formula[⊥,⊤,∨,∧] : ∀ ϱ →
  -----------------------------------
  Formula[⊥,⊤,∨,∧] (monCharFormula ϱ)
```

```
monCharFormula-soundness : ∀ ϱ →
  ---------------------------
  ⟦ monCharFormula ϱ ⟧ ϱ ≡ tt
```

```
monCharFormula-completeness : ∀ ϱ ϱ′ →
  ⟦ monCharFormula ϱ ⟧ ϱ′ ≡ tt →
  ---------------------------
  ϱ ≤V ϱ′
```

Notice that completeness is weaker than the corresponding property in !ref(charFormula-complete),
since it demands only `ϱ ≤V ϱ′` instead of `ϱ ≡ ϱ′`.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
monCharFormula-Formula[⊥,⊤,∨,∧] ϱ =
  Formula[⊥,⊤,∨,∧]-⋀-closed (map (monCharLit ϱ) propNames) all where

  all : All Formula[⊥,⊤,∨,∧] (map (monCharLit ϱ) propNames)
  all φ∈map
    with map-∈-inv _ φ∈map
  ... | p , _ , φ≡monCharLitϱp rewrite φ≡monCharLitϱp = monCharLit-Formula[⊥,⊤,∨,∧] ϱ p
```

Soundness and completeness of monotone characteristic formulas work as expected,
relying on the corresponding properties for literals:

```
monCharFormula-soundness ϱ = conjProp2 (map (monCharLit ϱ) propNames) ϱ go where

    go : ∀[ φ ∈ map (monCharLit ϱ) propNames ] ⟦ φ ⟧ ϱ ≡ tt
    go {φ} φ∈literals
      with map-∈-inv (monCharLit ϱ) φ∈literals
    ... | p , p∈propNames , φ≡monCharLitϱp
      rewrite φ≡monCharLitϱp | monCharLit-soundness ϱ p = refl
```

```
monCharFormula-completeness ϱ ϱ′ ⟦φ⟧ϱ′≡tt p
  with findPropName p
... | p∈propNames
  with map-∈ (monCharLit ϱ) p∈propNames
... | mCLϱp∈map
  with conjProp1 (map (monCharLit ϱ) propNames) ϱ′ ⟦φ⟧ϱ′≡tt mCLϱp∈map
... | ⟦mCLϱp⟧ϱ′≡tt = monCharLit-completeness ϱ p ϱ′ ⟦mCLϱp⟧ϱ′≡tt
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~


With all these ingredients in hand,
we are now ready to prove that the `{⊥, ⊤, ∨, ∧}` fragment is functionally complete for monotone functions:

```
MonotoneFunctionallyComplete : (Formula → Set) → Set
MonotoneFunctionallyComplete Fragment =
  ∀ f → Monotone f → ∃[ φ ] (Fragment φ × ⟦ φ ⟧_ ≡ f)

monFunCompl[⊥,⊤,∨,∧] : MonotoneFunctionallyComplete Formula[⊥,⊤,∨,∧]

monFunCompl[⊥,⊤,∨,∧] f monf = φ , Formula[⊥,⊤,∨,∧]φ , extensionality correctness where
```

The construction of the formula `φ` expressing `f` is analogous to !ref(funCompl[⊥,⊤,¬,∨,∧]),
except that !ref(〔_〕) is replaced by !ref(monCharFormula):

```
  ttVals = filter (λ ϱ → f ϱ ≡? tt) vals
  φs = map monCharFormula ttVals
  φ = ⋁ φs
```

The formula `φ` belongs to the fragment thanks to closure under disjunctions:

```
  Formula[⊥,⊤,∨,∧]φ : Formula[⊥,⊤,∨,∧] φ
  Formula[⊥,⊤,∨,∧]φ = Formula[⊥,⊤,∨,∧]-⋁-closed φs goal where

    goal : All Formula[⊥,⊤,∨,∧] φs
    goal φ∈φs
      with map-∈-inv _ φ∈φs
    ... | ϱ , _ , φ≡monCharFormulaϱ rewrite φ≡monCharFormulaϱ
      = monCharFormula-Formula[⊥,⊤,∨,∧] ϱ
```

Correctness consists into two parts.
The first part is easily proved by soundness:

```
  correctness : ∀ ϱ → ⟦ φ ⟧ ϱ ≡ f ϱ
  correctness ϱ
    with inspect (f ϱ)
  ... | it tt fϱ≡tt rewrite fϱ≡tt = goal where

    goal : ⟦ φ ⟧ ϱ ≡ tt
    goal
      with filter-∈ (findVal ϱ) fϱ≡tt
    ... | ϱ∈ttVals
      with map-∈ monCharFormula ϱ∈ttVals
    ... | monCharFormulaϱ∈φs
      with monCharFormula-soundness ϱ
    ... | ⟦monCharFormulaϱ⟧ϱ≡tt
      = disjProp-tt φs ϱ (monCharFormula ϱ) monCharFormulaϱ∈φs ⟦monCharFormulaϱ⟧ϱ≡tt 
```

For the second part, we aim at reaching a contradiction impinging on monotonicity:

```
  ... | it ff fϱ≡ff rewrite fϱ≡ff = disjProp-ff φs ϱ goal where

    goal : ∀[ φ ∈ φs ] ⟦ φ ⟧ ϱ ≡ ff
    goal {φ} φ∈φs
       with inspect (⟦ φ ⟧ ϱ)
    ... | it ff ⟦φ⟧ϱ≡ff = ⟦φ⟧ϱ≡ff
    ... | it tt ⟦φ⟧ϱ≡tt
      with map-∈-inv monCharFormula φ∈φs
    ... | ϱ′ , ϱ′∈ttVals , φ≡monCharFormulaϱ′
      with filter-∈-inv vals ϱ′∈ttVals 
    ... | ϱ′∈vals , fϱ′≡tt
      rewrite φ≡monCharFormulaϱ′
      with monCharFormula-completeness ϱ′ ϱ ⟦φ⟧ϱ≡tt 
    ... | ϱ′≤Vϱ
      with monf ϱ′ ϱ ϱ′≤Vϱ
    ... | fϱ′≤fϱ rewrite fϱ′≡tt | fϱ≡ff = tt≤𝔹ff-elim fϱ′≤fϱ
```

<!--

## Fragment `{∨, ∧, ⇒, ⊤}`

This fragment is not semantically complete.

-->

## Fragment `{⇑}` -- Sheffer's stroke {#Sheffer}

Since we cannot add a new connective,
we will define `⇑` in terms of previous connectives.

```

_⇑_ : Formula → Formula → Formula
φ ⇑ ψ = ¬ (φ ∧ ψ)

data Formula[⇑] : Formula → Set where
  `_ : ∀ p → Formula[⇑] (` p)
  _⟰_ : ∀ {φ ψ} → Formula[⇑] φ → Formula[⇑] ψ → Formula[⇑] (φ ⇑ ψ)

[∧,¬]→[⇑] : ∀ {φ} → Formula[¬∧] φ → Formula
[∧,¬]→[⇑] (` p) = ` p
[∧,¬]→[⇑] (¬ viewφ) with [∧,¬]→[⇑] viewφ
... | ψ = ψ ⇑ ψ
[∧,¬]→[⇑] (viewφ ∧ viewψ) with [∧,¬]→[⇑] viewφ | [∧,¬]→[⇑] viewψ
... | φ' | ψ' = let ξ = φ' ⇑ ψ' in ξ ⇑ ξ

[∧,¬]→[⇑]-fragment : ∀ {φ} (viewφ : Formula[¬∧] φ) →
  Formula[⇑] ([∧,¬]→[⇑] viewφ)
[∧,¬]→[⇑]-fragment (` p) = ` p
[∧,¬]→[⇑]-fragment (¬ viewφ)
  with [∧,¬]→[⇑]-fragment viewφ
... | viewψ = viewψ ⟰ viewψ
[∧,¬]→[⇑]-fragment (viewφ ∧ viewψ)
  with [∧,¬]→[⇑]-fragment viewφ | [∧,¬]→[⇑]-fragment viewψ
... | viewφ' | viewψ' = let viewξ = viewφ' ⟰ viewψ' in viewξ ⟰ viewξ

[∧,¬]→[⇑]-sound : ∀ {φ} (viewφ : Formula[¬∧] φ) →
  φ ⟺ [∧,¬]→[⇑] viewφ
[∧,¬]→[⇑]-sound (` p) ϱ = refl
[∧,¬]→[⇑]-sound (¬ viewφ) ϱ
  rewrite [∧,¬]→[⇑]-sound viewφ ϱ
  with ⟦ [∧,¬]→[⇑] viewφ ⟧ ϱ
... | tt = refl
... | ff = refl
[∧,¬]→[⇑]-sound (viewφ ∧ viewψ) ϱ
  rewrite [∧,¬]→[⇑]-sound viewφ ϱ | [∧,¬]→[⇑]-sound viewψ ϱ
  with ⟦ [∧,¬]→[⇑] viewφ ⟧ ϱ | ⟦ [∧,¬]→[⇑] viewψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl
```

# Solutions

!solutions
