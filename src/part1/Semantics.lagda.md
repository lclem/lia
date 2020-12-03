---
title: "Syntax and semantics of propositional logic 🚧"
---

In this chapter we introduce the syntax of propositional logic.

```
{-# OPTIONS --allow-unsolved-metas --rewriting --confluence-check #-} -- 
open import part0.index

module part1.Semantics (n' : ℕ) where
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

Our choice is to represent propositional variables with the datatype !remoteRef(part0)(Finite)(Fin).
The module parameter `n' : ℕ` allows us to name a fixed but arbitrary number of distinct propositions,
leading to the following definition (we omit the type annotation `Set`).

```
n = 3 + n'
PropName = Fin n
```

In examples, we use !ref(p₀), !ref(p₁), and !ref(p₂) as the following concrete variables [^10+n]:

```
p₀ p₁ p₂ : PropName
p₀ = fzero
p₁ = fsuc fzero 
p₂ = fsuc (fsuc fzero)
```

[^10+n]:
    With the simpler and perhaps more natural definition `PropName = Fin n′`
    we would not be able to name any specific proposition such as `p = fzero`
    since `n′` is arbitrary and in particular it could be `0`,
    i.e., there could be no proposition at all.


We use !ref(p), !ref(q), and !ref(r) as generic variable names,
which will be abstracted automatically as implicit arguments:

```
private
  variable
    p q r : PropName
```

Since propositions are modelled with !remoteRef(part0)(Finite)(Fin),
they inherit all the properties of the latter.
In particular, they enjoy decidable equality as initially required,

```
_ : p₀ ≡? p₀ ≡ yes _
_  = refl

_ : p₀ ≡? p₁ ≡ no _
_  = refl
```

and they can also be enumerated:

```
propNames : PropName *
propNames = enum

findPropName : ∀ p → p ∈ propNames
findPropName = find
```

For example, the first variable in the enumeration is !ref(p₀) and the second is !ref(p₁):

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
* the *true* constant $\top$ (pronounced "top"), or
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
    _∨_ _∧_ _⇒_ _⇔_ : (φ ψ : Formula) → Formula

private
  variable
    φ ψ : Formula
```

Note that there is a slight notation overload for variables `` ` p`` w.r.t. the pure mathematical syntax $p$
since we have to explicitly name the `` `_ `` constructor. The syntax for the other connectives is identical.

We follow standard notational conventions and assume that !ref(Formula)(¬_) is the operator with the highest priority
(i.e., it binds tighter than any other operator),
followed by !ref(Formula)(_∧_), !ref(Formula)(_∨_) and !ref(Formula)(_⇒_), and !ref(Formula)(_⇔_):

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

## Equality

From time to time we need to check whether two formulas are syntactically equal,
i.e., are the very same formula.
For example, `` ` p ∨ ` q`` is syntactically equal to itself,
but it is different from `` ` q ∨ ` p``.
A naïve way to decide equality would be to list all the 8 × 8 = 64 pairs of constructors,

    instance eqFormula : Eq (Formula)
    _≡?_ {{eqFormula}} = go where
      go : ∀ φ ψ → Dec (φ ≡ ψ)
      go ⊤ ⊤ = yes refl
      go ⊤ ⊥ = no λ ()
      go ⊤ (` _) = no λ ()
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
          go ⊤ ⊤ = yes refl
          go ⊤ _ = no (λ ())
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
  ... | yes eq = yes (c2ℕ-inj C1 C2 eq)
  -- by functionality
  ... | no neq = no λ{refl → neq refl}
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
Formula2Tree (φ ∨ ψ) = Node (left Or) ([ (Formula2Tree φ) (Formula2Tree ψ) ])
Formula2Tree (φ ∧ ψ) = Node (left And) ([ (Formula2Tree φ) (Formula2Tree ψ) ])
Formula2Tree (φ ⇒ ψ) = Node (left Implies) ([ (Formula2Tree φ) (Formula2Tree ψ) ])
Formula2Tree (φ ⇔ ψ) = Node (left Iff) ([ (Formula2Tree φ) (Formula2Tree ψ) ])
```

!exercise(#exercise:Formula2Tree-inj)(`Formula2Tree-inj`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove that the mapping `Formula2Tree` is injective.

```
Formula2Tree-inj : Injective Formula2Tree
```

*Hint:* Exploit the fact that the list constructor `_∷_` is injective on both arguments
(c.f. !remoteRef(part0)(List)(∷-inj-left) and !remoteRef(part0)(List)(∷-inj-right) from !chapterRef(part0)(List)).
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
we can show that `Formula` has decidable equality:

```
instance eqFormula : Eq Formula
_≡?_ {{eqFormula}} = go where
  
    go : ∀ φ ψ → Dec (φ ≡ ψ)
    go φ ψ with Formula2Tree φ ≡? Formula2Tree ψ
    ... | yes eq = yes (Formula2Tree-inj _ _ eq)
    ... | no neq = no λ{refl → neq refl}
```

!example(#example:equality)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We demonstrate decidability of formula equality. We have

```
_ : (` p₀ ∨ ` p₁ ≡? ` p₀ ∨ ` p₁) ≡ yes _
_ = refl
```

but

```
_ : (` p₀ ∨ ` p₁ ≡? ` p₁ ∨ ` p₀) ≡ no _
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

# Semantics

In this section we introduce the semantics of classical logic.

## Valuations

An *valuation* is a mapping that associates a Boolean value !remoteRef(part0)(Booleans)(𝔹) to each propositional variable.
We use !ref(ϱ) and !ref(ϱ′) for indicating a generic valuation.

```
Val = PropName → 𝔹

variable ϱ ϱ′ : Val
```

The two simplest valuations, and the least interesting,
are those which assign a constant truth value to every proposition:

```
ϱtt ϱff : Val
ϱtt = const tt
ϱff = const ff
```

As marginally more interesting example,
the valuation !ref(ϱ₀) below
assigns !remoteRef(part0)(Booleans)(𝔹)(ff) to `p₀` and `p₁`, and !remoteRef(part0)(Booleans)(𝔹)(tt) to every other variable:

```
ϱ₀ : Val
ϱ₀ = ϱtt [ p₀ ↦ ff ] [ p₁ ↦ ff ]
```

Since both propositions !ref(PropName) and Boolean values !remoteRef(part0)(Booleans)(𝔹) can be enumerated,
the same holds true for valuations !ref(Val),
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

* In the base cases !ref(Formula)(⊤) and !ref(Formula)(⊥),
the semantics is the corresponding truth value !remoteRef(part0)(Booleans)(𝔹)(tt), resp., !remoteRef(part0)(Booleans)(𝔹)(ff).
* In the variable case `` ` p ``, the semantics is `ϱ p` as provided by the valuation `ϱ`.
* In the negation case `¬ φ`, we inductively compute the semantics `⟦ φ ⟧ ϱ` of `φ`,
and then we apply the Boolean negation function [`¬𝔹_ : 𝔹 → 𝔹`](../../part0/Booleans#¬𝔹_).
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
(recall that both !ref(p₀) and !ref(p₁) evaluate to !remoteRef(part0)(Booleans)(ff) under !ref(ϱ₀)):

```
_ : ⟦ ` p₀ ∧ ¬ ` p₁ ⟧ ϱ₀ ≡ ff
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Invariance of the semantics

The semantics `⟦ φ ⟧ ϱ` of a formula `φ` depends on the valuation `ϱ`.
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
Intuitively, if two valuations `ϱ` and `ϱ′` agree (i.e., have the same value)
on the propositions `props φ` occurring in `φ`,
then the semantics is the same:

```
invariance : ∀ φ →
  Agree ϱ ϱ′ (props φ) →
  ------------------
  ⟦ φ ⟧ ϱ ≡ ⟦ φ ⟧ ϱ′
```

!exercise(#exercise:invariance)(`invariance`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove invariance of the semantics.
*Hint*: Proceed by structural induction on formulas. In the variable case, use the assumption `Agree ϱ ϱ′ (props φ)`.
In the inductive cases, use the fact that if `ϱ` and `ϱ′` agree on their value on the propositions in `φ ∧ ψ`,
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
Substitution binds tighter than !ref(Formula) constructors[^substitution-notation],
e.g., `¬ φ F[ p ↦ ξ ] ≡ ¬ (φ F[ p ↦ ξ ])`.
The definition of substitution follows a natural structural induction:

<!--
```
_ : ∀ φ p ξ →
  ----------------------------------
  ¬ φ F[ p ↦ ξ ] ≡ ¬ (φ F[ p ↦ ξ ])

_ = λ _ _ _ → refl
```
-->

[^substitution-notation]: Recall that the similar notation !remoteRef(part0)(Functions)(_[_↦_]) is reserved for function updates.

```
⊤ F[ _ ↦ ξ ] = ⊤
⊥ F[ p ↦ ξ ] = ⊥
(` q) F[ p ↦ ξ ] with p ≡? q
... | yes _ = ξ
... | no _ = ` q
(¬ φ) F[ p ↦ ξ ] = ¬ φ F[ p ↦ ξ ]
(φ ∧ ψ) F[ p ↦ ξ ] = φ F[ p ↦ ξ ] ∧ ψ F[ p ↦ ξ ]
(φ ∨ ψ) F[ p ↦ ξ ] = φ F[ p ↦ ξ ] ∨ ψ F[ p ↦ ξ ]
(φ ⇒ ψ) F[ p ↦ ξ ] = φ F[ p ↦ ξ ] ⇒ ψ F[ p ↦ ξ ]
(φ ⇔ ψ) F[ p ↦ ξ ] = φ F[ p ↦ ξ ] ⇔ ψ F[ p ↦ ξ ]
```

!example(#example:substitution)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We have

```
_ : (` p₀ ∨ ` p₁) F[ p₁ ↦ ` p₁ ∨ ` p₂ ] ≡ ` p₀ ∨ ` p₁ ∨ ` p₂
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:parallel-substitution)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
From time to time it is useful to substitute in parallel two propositions `p` and `q` by `ψ`, resp., `ξ`,
written `φ F2[ p , q ↦ ψ , ξ ]`.
For example, `` ` p₀ ∨ ` p₁ F2[ p₀ , p₁ ↦ p₁ , p₀ ] ≡ ` p₁ ∨ ` p₀ ``.
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
... | yes _ = ψ
... | no _
  with q ≡? r
... | yes _ = ξ
... | no _ = ` r

(¬ φ) F2[ p , q ↦ ψ , ξ ] = ¬ φ F2[ p , q ↦ ψ , ξ ]

(φ₁ ∧ φ₂) F2[ p , q ↦ ψ , ξ ] = φ₁ F2[ p , q ↦ ψ , ξ ] ∧ φ₂ F2[ p , q ↦ ψ , ξ ]

(φ₁ ∨ φ₂) F2[ p , q ↦ ψ , ξ ] = φ₁ F2[ p , q ↦ ψ , ξ ] ∨ φ₂ F2[ p , q ↦ ψ , ξ ]

(φ₁ ⇒ φ₂) F2[ p , q ↦ ψ , ξ ] = φ₁ F2[ p , q ↦ ψ , ξ ] ⇒ φ₂ F2[ p , q ↦ ψ , ξ ]

(φ₁ ⇔ φ₂) F2[ p , q ↦ ψ , ξ ] = φ₁ F2[ p , q ↦ ψ , ξ ] ⇔ φ₂ F2[ p , q ↦ ψ , ξ ]
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The main property of substitution regards its interaction with the semantics.
This is expressed by the following *substitution lemma*:

```
substitution : ∀ φ p ξ ϱ →
  --------------------------------------------
  ⟦ φ F[ p ↦ ξ ] ⟧ ϱ ≡ ⟦ φ ⟧ ϱ [ p ↦ ⟦ ξ ⟧ ϱ ]
```

Intuitively, the substitution lemma says that we can implement a syntactical substitution with a suitable update of the valuation.
One could say that the substitution lemma shows a certain *commutation rule* between substitution and evaluation.

!exercise(#exercise:substitution)(`substitution`) 
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the substitution lemma.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
substitution ⊤ p ξ ϱ = refl
substitution ⊥ p ξ ϱ = refl
substitution (` q) p ξ ϱ with p ≡? q
... | yes refl = refl
... | no _ = refl
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
subst-id : ∀ φ p ξ →
  p ~∈ props φ →
  ----------------
  φ F[ p ↦ ξ ] ≡ φ
```

*Hint:* Proceed by structural induction,
using the assumption `p ~∈ props φ` in the variable case;
the two auxiliary functions !remoteRef(part0)(List)(~∈-++-left) and !remoteRef(part0)(List)(~∈-++-right) will be useful in the inductive case.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
subst-id ⊤ p ξ p~∈φ = refl
subst-id ⊥ p ξ p~∈φ = refl
subst-id (` q) p ξ p~∈φ with p ≡? q
-- contradiction
... | yes refl = F-elim (p~∈φ here)
... | no _ = refl 
subst-id (¬ φ) p ξ p~∈φ
  rewrite subst-id φ p ξ p~∈φ = refl
subst-id (φ ∧ ψ) p ξ p~∈φ
  rewrite subst-id φ p ξ (~∈-++-left  p~∈φ) |
          subst-id ψ p ξ (~∈-++-right (props φ) p~∈φ) = refl 
subst-id (φ ∨ ψ) p ξ p~∈φ
  rewrite subst-id φ p ξ (~∈-++-left p~∈φ) |
          subst-id ψ p ξ (~∈-++-right (props φ) p~∈φ) = refl 
subst-id (φ ⇒ ψ) p ξ p~∈φ
  rewrite subst-id φ p ξ (~∈-++-left p~∈φ) |
          subst-id ψ p ξ (~∈-++-right (props φ) p~∈φ) = refl 
subst-id (φ ⇔ ψ) p ξ p~∈φ
  rewrite subst-id φ p ξ (~∈-++-left p~∈φ) |
          subst-id ψ p ξ (~∈-++-right (props φ) p~∈φ) = refl 
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:rename-undo)(`rename-undo`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Let `φ : Formula` be a formula and `p q : PropName` two propositions.
Prove that a double substitution ``φ F[ p ↦ ` q ] F[ q ↦ ` p ]`` does not change the formula `φ`
if the variable `q` does not occur in `φ`:

```
rename-undo : ∀ φ p q →
  q ∉ props φ →
  --------------------------------
  φ F[ p ↦ ` q ] F[ q ↦ ` p ] ≡ φ
```

**Warning**: `q ∉ props φ` here is different from `q ~∈ props φ`.
While the latter is just an abbreviation for `~ (q ∈ props φ)`
and thus it provides indirect evidence that `q` is not in `props φ`,
the former provides direct evidence that `q` is not in `props φ`
and thus it is stronger.
The two happen to be equivalent thanks to the conversion functions
!remoteRef(part0)(List)(~∈→∉) and !remoteRef(part0)(List)(∉→~∈)

*Hint:* Proceed by induction on the evidence `q ∉ props φ` that `q` is not in `φ`.
The auxiliary functions !remoteRef(part0)(List)(∉-++-left) and !remoteRef(part0)(List)(∉-++-right) will be useful in the inductive cases.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
rename-undo ⊤ p q q∉φ = refl
rename-undo ⊥ p q q∉φ = refl

rename-undo (` r) p q (notThere q≢r _)
  with refl-≡? q
... | q≡?q≡yes
  with p ≡? r
... | yes refl rewrite q≡?q≡yes = refl 
... | no _
  with q ≡? r
... | yes refl = x≢x-elim q≢r
... | no _ = refl 

rename-undo (¬ φ) p q q∉φ
  rewrite rename-undo φ p q q∉φ = refl

rename-undo (φ ∧ ψ) p q q∉φ
  rewrite rename-undo φ p q (∉-++-left q∉φ) |
          rename-undo ψ p q (∉-++-right {as = props φ} q∉φ)
  = refl
  
rename-undo (φ ∨ ψ) p q q∉φ
  rewrite rename-undo φ p q (∉-++-left q∉φ) |
          rename-undo ψ p q (∉-++-right {as = props φ} q∉φ)
  = refl
  
rename-undo (φ ⇒ ψ) p q q∉φ
  rewrite rename-undo φ p q (∉-++-left q∉φ) |
          rename-undo ψ p q (∉-++-right {as = props φ} q∉φ)
  = refl
  
rename-undo (φ ⇔ ψ) p q q∉φ
  rewrite rename-undo φ p q (∉-++-left q∉φ) |
          rename-undo ψ p q (∉-++-right {as = props φ} q∉φ)
  = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Tautology, entailment, and equivalence

### Tautology

A *tautology* is a formula that evaluates to !remoteRef(part0)(Booleans)(𝔹)(tt) under every valuation:

```
Tautology : Formula → Set
Tautology φ = ∀[ ϱ ] ⟦ φ ⟧ ϱ ≡ tt
```

For instance the *law of excluded middle* `` ` p ∨ ¬ ` p ``,
which amounts to say that the propositional variable `p` has either the value !remoteRef(part0)(Booleans)(𝔹)(tt) or !remoteRef(part0)(Booleans)(𝔹)(ff),
is a tautology of classical logic:

```
LEM : Tautology (` p ∨ ¬ ` p)
LEM {p} ϱ with ϱ p
... | tt = refl
... | ff = refl
```

On the other hand, `` ` p `` is not a tautology since the (any) valuation that maps `p` to !remoteRef(part0)(Booleans)(𝔹)(ff), such as `const ff`, does not satisfy it:

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

For instance, we can check by computing that `` ` p₀ ∨ ¬ ` p₀ `` is a tautology,
and that `` ` p₀ ∨ ` p₁ `` is not a tautology,
where !ref(p₀) and !ref(p₁) are two concrete propositions.

```
_ : n ≡ 3 → ⌞ Tautology? (` p₀ ∨ ¬ ` p₀) ⌟ ≡ tt
_ = λ{refl → refl}

_ : n ≡ 3 → ⌞ Tautology? (` p₀ ∨ ¬ ` p₁) ⌟ ≡ ff
_ = λ{refl → refl}
```

(Note that we need to assume that !ref(n) is some concrete number here,
allowing us to actually enumerate all valuations.
 We use the erasure mapping !remoteRef(part0)(Booleans)(⌞_⌟) to convert !remoteRef(part0)(Decidable)(Dec)(yes), resp., !remoteRef(part0)(Decidable)(Dec)(no), to !remoteRef(part0)(Booleans)(𝔹)(tt), resp., !remoteRef(part0)(Booleans)(𝔹)(ff),
thus discarding the proof of correctness returned by !ref(Tautology?).)

!exercise(#exercise:tautology-substitution)(Tautology and substitution)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Show that if `φ` is a tautology, then replacing any propositional variable therein with an arbitrary formula is also a tautology:
```
tautology-subst : ∀ φ p ψ →
  Tautology φ →
  -------------------------
  Tautology (φ F[ p ↦ ψ ])
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The proof is an immediate application of the substitution lemma:

```
tautology-subst φ p ψ tau-φ ϱ
  rewrite substitution φ p ψ ϱ = tau-φ (ϱ [ p ↦ ⟦ ψ ⟧ ϱ ])
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
entailment !ref(_⇛_) shoud not be confused with the formula implication constructor [`_⇒_ : Formula → Formula → Formula`](#Formula._⇒_);
the same warning applies to logical equivalence !ref(_⟺_) vs. the bi-implication constructor !ref(Formula)(_⇔_).)
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
_ : n ≡ 3 → ⌞ ` p₀ ⇛? ` p₀ ∨ ` p₁ ⌟ ≡ tt
_ = λ{refl → refl}

_ : n ≡ 3 → ⌞ ` p₀ ⇛? ` p₁ ⌟ ≡ ff
_ = λ{refl → refl}

_ : n ≡ 3 → ⌞ ` p₀ ∧ ` p₁ ⟺? ` p₁ ∧ ` p₀ ⌟ ≡ tt
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

The fact that entailment is a preodrer implies immediately that logical equivalence is also a prerorder.

```
refl-⟺ : ∀ φ → φ ⟺ φ
sym-⟺ : ∀ φ ψ → φ ⟺ ψ → ψ ⟺ φ
trans-⟺ : ∀ φ ψ ξ → φ ⟺ ψ → ψ ⟺ ξ → φ ⟺ ξ
```

!hide
~~~~~~~~

~~~~~~~~
~~~~~~~~
```
refl-⟺ = {!!}
trans-⟺ = {!!}
sym-⟺ = {!!}
```
~~~~~~~~

There is a simple reprhasing of tautology in terms of logical equivalence.
A formula `φ` is a tautology iff it is logically equivalent to !ref(Formula)(⊤):

```
tautology-equivalence : ∀ φ → Tautology φ ↔ φ ⟺ ⊤
tautology-equivalence φ = (λ tau ϱ → tau ϱ) , λ φ⟺⊤ ϱ → φ⟺⊤ ϱ
```

While quite evident by itself, the equivalence above does find its applications,
such as in !remoteRef(part1)(CharacteristicFormulas)(duality-tautology).

TODO: put this in context:

```
tautology-impl : 
  Tautology φ →
  φ ⇛ ψ →
  ------------
  Tautology ψ

tautology-impl = {!   !}
```


The following exercise explores a converse relationship between entailment/equivalnce and tautology.

!exercise(#exercise:entailment-implication)(Entailment and implication)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The typographic similarity betwee entailment and implication,
and similarly for equivalence and bi-implication,
is explained by the following connection with tautology:

```
entailment-implication : ∀ φ ψ → φ ⇛ ψ ↔ Tautology (φ ⇒ ψ)
entailment-equivalence : ∀ φ ψ → φ ⟺ ψ ↔ Tautology (φ ⇔ ψ)
```

Prove the two properties above.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We begin with !ref(entailment-implication).
We break it up into two directions, which are proved separately:

```
entailment-implication-1 : ∀ φ ψ →
  φ ⇛ ψ →
  ------------------
  Tautology (φ ⇒ ψ)

entailment-implication-1 φ ψ φ⇛ψ ϱ
  with inspect (⟦ φ ⟧ ϱ)
... | it tt ⟦φ⟧ϱ=tt
  rewrite ⟦φ⟧ϱ=tt | φ⇛ψ ϱ ⟦φ⟧ϱ=tt = refl
... | it ff ⟦φ⟧ϱ=ff
  rewrite ⟦φ⟧ϱ=ff = refl
```

```
entailment-implication-2 : ∀ φ ψ →
  Tautology (φ ⇒ ψ) →
  ------------------
  φ ⇛ ψ
 
entailment-implication-2 φ ψ tau ϱ ⟦φ⟧ϱ≡tt = ⟦ψ⟧ϱ≡tt where

  have : ⟦ φ ⟧ ϱ ⇒𝔹 ⟦ ψ ⟧ ϱ ≡ tt
  have = tau ϱ

  equiv : ⟦ φ ⟧ ϱ ⇒𝔹 ⟦ ψ ⟧ ϱ ≡ ⟦ ψ ⟧ ϱ
  equiv = 𝔹implProp2 (⟦ φ ⟧ ϱ) (⟦ ψ ⟧ ϱ) ⟦φ⟧ϱ≡tt

  ⟦ψ⟧ϱ≡tt : ⟦ ψ ⟧ ϱ ≡ tt
  ⟦ψ⟧ϱ≡tt rewrite sym equiv = have
```

We put the two directions together:

```
entailment-implication φ ψ = entailment-implication-1 φ ψ , entailment-implication-2 φ ψ
```

The treatment for equivalence:

```
entailment-equivalence φ ψ = {!!}
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Some equivalences require no computation at all:

```
¬¬⊤⟺⊤ : ¬ ¬ ⊤ ⟺ ⊤
¬¬⊤⟺⊤ ϱ = refl
```

More elaborate equivalences require marginally more work,
as shown in the next exercise.

!exercise(#exercise:common-equivalences)(Common equivalences)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the folowing equivalences.
*Hint:* Use the method of truth tables.

```
idempotAnd : ∀ φ → φ ∧ φ ⟺ φ

commAnd : ∀ φ ψ → φ ∧ ψ ⟺ ψ ∧ φ
commOr : ∀ φ ψ → φ ∨ ψ ⟺ ψ ∨ φ

assocOr : ∀ φ ψ ξ → (φ ∨ ψ) ∨ ξ ⟺ φ ∨ ψ ∨ ξ
assocAnd : ∀ φ ψ ξ → (φ ∧ ψ) ∧ ξ ⟺ φ ∧ ψ ∧ ξ

distrAndOr-left : ∀ φ ψ ξ → φ ∧ (ψ ∨ ξ) ⟺ φ ∧ ψ ∨ φ ∧ ξ
distrAndOr-right : ∀ φ ψ ξ → (φ ∨ ψ) ∧ ξ ⟺ φ ∧ ξ ∨ ψ ∧ ξ

expandImplies : ∀ φ ψ → φ ⇒ ψ ⟺ ¬ φ ∨ ψ
expandIff : ∀ φ ψ → φ ⇔ ψ ⟺ (¬ φ ∨ ψ) ∧ (φ ∨ ¬ ψ)

doubleNegationLaw : ∀ φ → ¬ ¬ φ ⟺ φ
deMorganAnd : ∀ φ ψ → ¬ (φ ∧ ψ) ⟺ ¬ φ ∨ ¬ ψ
deMorganOr : ∀ φ ψ → ¬ (φ ∨ ψ) ⟺ ¬ φ ∧ ¬ ψ
deMorganOr-alt : ∀ φ ψ → φ ∨ ψ ⟺ ¬ (¬ φ ∧ ¬ ψ)
deMorganImplies : ∀ φ ψ → ¬ (φ ⇒ ψ) ⟺ φ ∧ ¬ ψ
deMorganIff-left : ∀ φ ψ → ¬ (φ ⇔ ψ) ⟺ ¬ φ ⇔ ψ
deMorganIff-right : ∀ φ ψ → ¬ (φ ⇔ ψ) ⟺ φ ⇔ ¬ ψ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
idempotAnd φ ϱ = idempot-∧𝔹 (⟦ φ ⟧ ϱ)

commAnd φ ψ ϱ = comm-∧𝔹 (⟦ φ ⟧ ϱ) (⟦ ψ ⟧ ϱ)
commOr φ ψ ϱ = comm-∨𝔹 (⟦ φ ⟧ ϱ) (⟦ ψ ⟧ ϱ)

assocOr φ ψ ξ ϱ = assoc-∨𝔹 (⟦ φ ⟧ ϱ) (⟦ ψ ⟧ ϱ) (⟦ ξ ⟧ ϱ)
assocAnd φ ψ ξ ϱ = assoc-∧𝔹 (⟦ φ ⟧ ϱ) (⟦ ψ ⟧ ϱ) (⟦ ξ ⟧ ϱ)
distrAndOr-left φ ψ ξ ϱ = distr-left-∧∨𝔹 (⟦ φ ⟧ ϱ) (⟦ ψ ⟧ ϱ) (⟦ ξ ⟧ ϱ)
distrAndOr-right φ ψ ξ ϱ = distr-right-∧∨𝔹 (⟦ φ ⟧ ϱ) (⟦ ψ ⟧ ϱ) (⟦ ξ ⟧ ϱ)

expandImplies φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

expandIff φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

doubleNegationLaw φ ϱ with ⟦ φ ⟧ ϱ
... | tt = refl
... | ff = refl

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

deMorganIff-left φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

deMorganIff-right φ ψ ϱ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

### Equivalence is a congruence

Logical equivalence is a *congruence*,
in the sense that replacing a formula with an equivalent one preserves the semantics:

```
congF : ∀ φ ψ ξ p →
  φ ⟺ ψ →
  -----------------------------
  ξ F[ p ↦ φ ] ⟺ ξ F[ p ↦ ψ ]
```

!hide
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The proof follows a straightforward structural induction.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
congF _ _ ⊤ p φ⟺ψ ϱ = refl

congF _ _ ⊥ p φ⟺ψ ϱ = refl

congF _ _ (` q) p φ⟺ψ ϱ
  with p ≡? q
... | yes _ = φ⟺ψ ϱ
... | no _ = refl

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
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
... | yes _ = φ₀⟺ψ₀ ϱ
... | no _
  with p₁ ≡? p
... | yes _ = φ₁⟺ψ₁ ϱ
... | no _ = refl

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

The congruence properties !ref(congF) and !ref(cong2F) are very convenient to quickly show correctness of many formula transformations
(such as those in [Functional completeness](#Functional-Completeness) below and in transformations to [normal forms](../../part1/NormalForms).

## Satisfiability

A formula `φ` is *satisfiable* if there exists some valuation satisfying it:

```
Sat : Formula → Set
Sat φ = ∃[ ϱ ] ⟦ φ ⟧ ϱ ≡ tt
```

Satisfiability is decidable (for every fixed number of propositional variables)
since we can enumerate satisfying assignments:

```
Sat? : ∀ φ → Dec (Sat φ)
Sat? φ = ∃?[ ϱ ] ⟦ φ ⟧ ϱ ≡? tt
```

For instance, the formula `` ` p₀ ∧ ¬ ` p₁ `` is satisfiable,
however `` ` p₀ ∧ ¬ ` p₀ `` is not:

```
_ : n ≡ 3 → ⌞ Sat? (` p₀ ∧ ¬ ` p₁) ⌟ ≡ tt
_ = λ{refl → refl}

_ : n ≡ 3 → ⌞ Sat? (` p₀ ∧ ¬ ` p₀) ⌟ ≡ ff
_ = λ{refl → refl}
```

Of course we can also prove that the latter formula is unsatisfiable for *every* number of variables:

```
p∧¬p-unsat : ~ Sat (` p ∧ ¬ ` p)
p∧¬p-unsat {p} (ϱ , equiv) with ϱ p
... | tt = ff≢tt equiv
... | ff = ff≢tt equiv
```

!exercise(#exercise:tau-sat)(Tautology and satisfiability)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Elaborate and prove a natural property connecting whether `φ` is a tautology and satisfiability.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
One possible property is the following:

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

!exercise(#exercise:equiv-unsat)(Equivalence and unsatisfiability)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Express unsatisfiability in terms of logical equivalence.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
One possible property is that a formula is unsatisfiable if, and only if, it is logically equivalent to !ref(⊥):

```
equiv↔unsat : φ ⟺ ⊥ ↔ ~ Sat φ
```

We prove the two directions separately:

```
equiv→unsat : φ ⟺ ⊥ → ~ Sat φ
equiv→unsat φ⟺⊥ (ϱ , ⟦φ⟧ϱ≡tt)
  with φ⟺⊥ ϱ
... | ⟦φ⟧ϱ≡ff = a≡ff→a≡tt-elim ⟦φ⟧ϱ≡ff ⟦φ⟧ϱ≡tt
```

```
unsat→equiv : ~ Sat φ → φ ⟺ ⊥
unsat→equiv {φ} ~Satφ ϱ
  with inspect (⟦ φ ⟧ ϱ)
... | it ff ⟦φ⟧ϱ≡ff = ⟦φ⟧ϱ≡ff
... | it tt ⟦φ⟧ϱ≡tt = F-elim (~Satφ (ϱ , ⟦φ⟧ϱ≡tt))
```

It is now just a matter of combining the two directions:

```
equiv↔unsat {φ} = equiv→unsat {φ} , unsat→equiv {φ}
```

For instance, we can prove:

```
p∧¬p⟺⊥ : ` p ∧ ¬ ` p ⟺ ⊥
p∧¬p⟺⊥ {p} ϱ = unsat→equiv {` p ∧ ¬ ` p} p∧¬p-unsat ϱ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Long conjunctions and disjunctions

### Conjunctions

Sometimes it is useful to interpret a list of formulas as their conjunction.
This is achieved with the following "long conjunction" operation:

```
infix 10 ⋀_
⋀_ : Formula * → Formula
⋀ φs = foldr1 _∧_ ⊤ φs
```

(Despite the typographical similarity,
!ref(⋀_) is a unary function mapping lists of formulas to their logical conjunction,
while [`_∧_ : Formula → Formula → Formula`](#Formula._∧_) is a binary formula constructor.)
For instance, we have

```
_ : ⋀ [ (` p₀) (` p₁) (` p₂) ] ≡ ` p₀ ∧ ` p₁ ∧ ` p₂
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
Prove the two defining properties !ref(conjProp1) and !ref(conjProp2) of long conjunctions
*Hint:* Use the corresponding properties for Booleans.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
conjProp1 (ψ ∷ ε) ϱ ⟦φs⟧≡tt here = 𝔹conjProp1 (⟦ ψ ⟧ ϱ) tt ⟦φs⟧≡tt
conjProp1 (ψ ∷ φs@(_ ∷ _)) ϱ ⟦φs⟧≡tt here = 𝔹conjProp1 (⟦ ψ ⟧ ϱ) (⟦ ⋀ φs ⟧ ϱ) ⟦φs⟧≡tt 
conjProp1 (ψ ∷ φs@(_ ∷ _)) ϱ ⟦ψ∧φs⟧≡tt {φ} (there φ∈φs)
  = conjProp1 φs ϱ (𝔹conjProp2 (⟦ ψ ⟧ ϱ) _ ⟦ψ∧φs⟧≡tt) φ∈φs 

conjProp2 ε ϱ ass = refl
conjProp2 (φ ∷ ε) ϱ ass = ass here
conjProp2 (φ ∷ φs@(_ ∷ _)) ϱ ass
  with conjProp2 φs ϱ λ ψ∈φs → ass (there ψ∈φs)
... | ⟦⋀φs⟧ϱ≡tt = 𝔹conjProp3 _ _ ⟦φ⟧ϱ≡tt ⟦⋀φs⟧ϱ≡tt where

  ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
  ⟦φ⟧ϱ≡tt = ass here
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
Prove the two defining properties !ref(disjProp-tt) and !ref(disjProp-ff) above.
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

private
  variable
    Γ Δ : Context
```

If `Γ` is a context and `φ` is a formula,
then we can add `φ` to `Γ` and form the new context `Γ · φ`
(this is just adding an element in front of a list but written on the right).

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

The semantic deduction theorem establishes a close connection between the implication connective !ref(Formula)(_⇒_),
which is a syntactic object,
and entailment !ref(_⊨_), which is a semantic one.
It consists of two halves.
The first half shows how to move a formula from the formula to the context:

```
semDT1 : ∀ φ ψ →
  Γ ⊨ φ ⇒ ψ →
  ---------
  Γ · φ ⊨ ψ
```

The second half shows the converse operation:

```
semDT2 : ∀ φ ψ →
  Γ · φ ⊨ ψ →
  ----------
  Γ ⊨ φ ⇒ ψ
```

!exercise(#exercise:sem-DT)(Semantic deduction theorem)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove the two parts !ref(semDT2) and !ref(semDT1) of the semantic deduction theorem.
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
semDT2 {Γ} ψ φ Γ·ψ⊨φ = Δ⊨ψ⇒φ where

  Δ⊨ψ⇒φ : Γ ⊨ ψ ⇒ φ
  Δ⊨ψ⇒φ ϱ ⟦Γ⟧ with inspect (⟦ ψ ⟧ ϱ)
  ... | it ff ⟦ψ⟧ϱ≡ff rewrite ⟦ψ⟧ϱ≡ff = refl
  ... | it tt ⟦ψ⟧ϱ≡tt rewrite ⟦ψ⟧ϱ≡tt = trans eql ⟦φ⟧ϱ≡tt where

    eql : tt ⇒𝔹 ⟦ φ ⟧ ϱ ≡ ⟦ φ ⟧ ϱ
    eql = 𝔹implProp2 _ _ refl
    
    ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
    ⟦φ⟧ϱ≡tt = Γ·ψ⊨φ ϱ ⟦ψ∷Γ⟧ where

      ⟦ψ∷Γ⟧ : ∀[ ξ ∈ ψ ∷ Γ ] ⟦ ξ ⟧ ϱ ≡ tt
      ⟦ψ∷Γ⟧ here = ⟦ψ⟧ϱ≡tt
      ⟦ψ∷Γ⟧ (there ξ∈Γ) = ⟦Γ⟧ ξ∈Γ

semDT1 {Γ} φ ψ Γ⊨φ⇒ψ ϱ AllΓ·φ = ⟦ψ⟧ϱ≡tt where

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

TODO: put it in context as an application of DT

```
modus-ponens : ∀ {Γ} φ ψ →
  Γ ⊨ φ ⇒ ψ →
  Γ ⊨ φ →
  ------
  Γ ⊨ ψ

modus-ponens φ ψ Γ⊨φ⇒ψ Γ⊨φ ϱ x
 with semDT1 φ ψ Γ⊨φ⇒ψ
... | Γ·φ⊨ψ = Γ·φ⊨ψ ϱ λ{ here → Γ⊨φ ϱ x
                        ; (there y) → x y}
```

We can now state the following "long" versions of the semantic deduction theorem.

```
longSemDT1 :
  Δ ⊨ φ →
  -------------
  ∅ ⊨ Δ Imply φ

longSemDT2 :
  ∅ ⊨ Δ Imply φ →
  -----
  Δ ⊨ φ
```

!hide
~~~~~~~~~
The proofs are a straightforward applications of !ref(semDT2) and !ref(semDT1).
~~~~~~~~~
~~~~~~~~~
```
longSemDT1 {ε} {φ} ε⊨φ = ε⊨φ
longSemDT1 {ψ ∷ Δ} {φ} ψ∷Δ⊨φ = longSemDT1 {Δ} {ψ ⇒ φ} (semDT2 ψ φ ψ∷Δ⊨φ)

longSemDT2 {ε} {φ} ∅⊨φ ϱ All∅ = ∅⊨φ ϱ All∅
longSemDT2 {ψ ∷ Δ} {φ} ∅⊨ΔImplyφ = semDT1 ψ φ (longSemDT2 {Δ} {ψ ⇒ φ} ∅⊨ΔImplyφ)
```
~~~~~~~~~

# Formula simplification

In this section we present a procedure to simplify formulas.
We start with a simple use case to illustrate some practical difficulties that naturally arise.
Suppose we want to remove a single outmost double negation `¬ ¬ φ` in a formula.
A natural definition would be the following:

```
remove-¬¬1 : Formula → Formula
remove-¬¬1 (¬ ¬ φ) = φ
remove-¬¬1 φ = φ
```

The next step is to prove that the definition above is correct:

```
remove-¬¬1-correctness : ∀ φ → φ ⟺ remove-¬¬1 φ
```

Due to the nature of pattern matching in Agda,
the following does not work as expected:

    remove-¬¬1-correctness (¬ ¬ φ) ϱ = refl
    remove-¬¬1-correctness φ ϱ = refl

The interpreter is not able to expand `remove-¬¬1 φ` into `φ` in the second clause.
In order to trigger evaluation, we need to convince the interpreter that `φ` is not of the form `¬ ¬ ψ`,
requiring us to list many more cases that we may like to:

!hide
~~~~~~
```
remove-¬¬1-correctness (¬ ¬ φ) ϱ = refl
remove-¬¬1-correctness ⊥ ϱ = refl
remove-¬¬1-correctness ⊤ ϱ = refl
{- ... and many more ... -}
```
~~~~~~
~~~~~~
```
remove-¬¬1-correctness (` p) ϱ = refl
remove-¬¬1-correctness (¬ ⊥) ϱ = refl
remove-¬¬1-correctness (¬ ⊤) ϱ = refl
remove-¬¬1-correctness (¬ ` p) ϱ = refl
remove-¬¬1-correctness (¬ (φ ∨ ψ)) ϱ = refl
remove-¬¬1-correctness (¬ (φ ∧ ψ)) ϱ = refl
remove-¬¬1-correctness (¬ (φ ⇒ ψ)) ϱ = refl
remove-¬¬1-correctness (¬ (φ ⇔ ψ)) ϱ = refl
remove-¬¬1-correctness (φ ∨ ψ) ϱ = refl
remove-¬¬1-correctness (φ ∧ ψ) ϱ = refl
remove-¬¬1-correctness (φ ⇒ ψ) ϱ = refl
remove-¬¬1-correctness (φ ⇔ ψ) ϱ = refl
```
~~~~~~

## Views

The standard solution in a case like this is to use *views* [@Wadler:POPL:1987;@McBrideMcKinna:JFL:2004].

An inductive definition such as !ref(Formula) provides what we may call the "default view",
i.e., whether a formula is !ref(Formula)(⊥), !ref(Formula)(⊤), and so on.
A definition by structural recursion on !ref(Formula) such as !ref(⟦_⟧_) is using this default view.

When the default view is not adequate, we can define alternative views (presentations) of the same data.
In our use case, the view should reflect the recursive structure of !ref(remove-¬¬1).
We may thus say that a view is a means to encode recursion into data.
In our example, we will have two constructors,
depending on whether the formula is a double negation or not:

```
data Remove-¬¬-View : Formula → Set where
  go-¬¬ : ∀ ψ → Remove-¬¬-View (¬ ¬ ψ)
  stop : ∀ ψ → Remove-¬¬-View ψ
```

A view for formulas has the general type `Formula → Set`,
and can thus be thought of as a property of formulas.
The peculiar things about views is that every formula will have a view for it
(after all we are encoding total functions).
The following unsurprising function computes the view corresponding to the input formula:

```
remove-¬¬-View : ∀ φ → Remove-¬¬-View φ
remove-¬¬-View (¬ ¬ φ) = go-¬¬ φ
remove-¬¬-View φ = stop φ
```

The function !ref(remove-¬¬-View) is as simple as it gets.
In particular, we can use the catch-all pattern in the second case to already decide that the output will be `stop φ`.
Once we have a way of computing the view of interest,
we can use it to encode !ref(remove-¬¬) and its correctness proof !ref(remove-¬¬-correctness):

```
remove-¬¬ : Formula → Formula
remove-¬¬ φ with remove-¬¬-View φ
... | go-¬¬ ψ = ψ
... | stop ψ = ψ
```

```
remove-¬¬-correctness : ∀ φ → φ ⟺ remove-¬¬ φ
remove-¬¬-correctness φ ϱ with remove-¬¬-View φ
... | go-¬¬ ψ = refl
... | stop ψ = refl
```

It is instructive to compare !ref(remove-¬¬-correctness) with !ref(remove-¬¬1-correctness) w.r.t. size.

Views may look a little roundabout at first.
One may wonder whether the following simpler datatype may work too:

```
data Remove-¬¬-View′ : Set where
  go-¬¬′ : Remove-¬¬-View′
  stop′ : Remove-¬¬-View′

remove-¬¬-View′ : Formula → Remove-¬¬-View′
remove-¬¬-View′ (¬ ¬ φ) = go-¬¬′
remove-¬¬-View′ φ = stop′
```

However, the simpler !ref(Remove-¬¬-View′) is insufficient
since we lose track of the connection between the view and the formula it is a view of.
For instance, we immediately run into trouble when defining `remove-¬¬′`:

    remove-¬¬′ : Formula → Formula
    remove-¬¬′ φ with remove-¬¬-View′ φ
    remove-¬¬′ (¬ ¬ ψ) | go-¬¬′ = ψ
    remove-¬¬′ φ | stop′ = φ

The interpreter complains that there are missing cases,
such as `remove-¬¬′ ⊥ | go-¬¬′`, `remove-¬¬′ ⊤ | go-¬¬′`, and so on.
The additional power of views is that the interpeter knows from the constructor to which formula does the view correspond,
and thus it is able to figure out that the definition in !ref(remove-¬¬) is complete.

## Full fledged simplification

After this introduction on views,
we can present a more powerful simplification procedure.
Our aim is to

- remove the constants !ref(Formula)(⊥) and !ref(Formula)(⊤) (unless this is all what the formula is), and
- remove double negations `¬ ¬ φ`.

To this end, we define the following view:

```
data SimplifyView : Formula → Set where

  ¬⊥ : SimplifyView (¬ ⊥)
  ¬⊤ : SimplifyView (¬ ⊤)
  ¬¬_ : ∀ ψ → SimplifyView (¬ ¬ ψ)

  ⊥∨_ : ∀ ψ → SimplifyView (⊥ ∨ ψ)
  _∨⊥ : ∀ ψ → SimplifyView (ψ ∨ ⊥)
  ⊤∨_ : ∀ ψ → SimplifyView (⊤ ∨ ψ)
  _∨⊤ : ∀ ψ → SimplifyView (ψ ∨ ⊤)
  
  ⊥∧_ : ∀ ψ → SimplifyView (⊥ ∧ ψ)
  _∧⊥ : ∀ ψ → SimplifyView (ψ ∧ ⊥)
  ⊤∧_ : ∀ ψ → SimplifyView (⊤ ∧ ψ)
  _∧⊤ : ∀ ψ → SimplifyView (ψ ∧ ⊤)
  
  ⊥⇒_ : ∀ ψ → SimplifyView (⊥ ⇒ ψ)
  _⇒⊥ : ∀ ψ → SimplifyView (ψ ⇒ ⊥)
  ⊤⇒_ : ∀ ψ → SimplifyView (⊤ ⇒ ψ)
  _⇒⊤ : ∀ ψ → SimplifyView (ψ ⇒ ⊤)
  
  ⊥⇔_ : ∀ ψ → SimplifyView (⊥ ⇔ ψ)
  _⇔⊥ : ∀ ψ → SimplifyView (ψ ⇔ ⊥)
  ⊤⇔_ : ∀ ψ → SimplifyView (⊤ ⇔ ψ)
  _⇔⊤ : ∀ ψ → SimplifyView (ψ ⇔ ⊤)
  
  stop : ∀ ψ → SimplifyView ψ  
```

We have one constructor for each kind of subformula that we want to reduce.
The view `⊥∨ ψ` is designed to look typographically similar to the underlying formula `⊥ ∨ ψ` for suggestive purposes,
and similarly for the others.
However, it is important to keep in mind that the latter is of type !ref(Formula),
while the former is of type `SimplifyView (⊥ ∨ ψ)`.
The last constructor `stop φ` signals that no further simplification is available.
The following function computes the view:

```
simplifyView : ∀ φ → SimplifyView φ
```

!hide
~~~~~~~~
Its definition is unimaginative.
~~~~~~~~
~~~~~~~~
```
simplifyView (¬ ⊥) = ¬⊥
simplifyView (¬ ⊤) = ¬⊤
simplifyView (¬ ¬ φ) = ¬¬ φ

simplifyView (⊥ ∨ φ) = ⊥∨ φ
simplifyView (φ ∨ ⊥) = φ ∨⊥
simplifyView (⊤ ∨ φ) = ⊤∨ φ
simplifyView (φ ∨ ⊤) = φ ∨⊤

simplifyView (⊥ ∧ φ) = ⊥∧ φ
simplifyView (φ ∧ ⊥) = φ ∧⊥
simplifyView (⊤ ∧ φ) = ⊤∧ φ
simplifyView (φ ∧ ⊤) = φ ∧⊤

simplifyView (⊥ ⇒ φ) = ⊥⇒ φ
simplifyView (φ ⇒ ⊥) = φ ⇒⊥
simplifyView (⊤ ⇒ φ) = ⊤⇒ φ
simplifyView (φ ⇒ ⊤) = φ ⇒⊤

simplifyView (⊥ ⇔ φ) = ⊥⇔ φ
simplifyView (φ ⇔ ⊥) = φ ⇔⊥
simplifyView (⊤ ⇔ φ) = ⊤⇔ φ
simplifyView (φ ⇔ ⊤) = φ ⇔⊤

simplifyView φ = stop φ
```
~~~~~~~~

It is convenient to define the simplification procedure in two separate functions,

```
simplify1 simplify : Formula → Formula
```

The first function !ref(simplify1) is non-recursive and it defines a single simplification step
in terms of the view of the formula:

```
simplify1 φ
  with simplifyView φ
... | ¬⊥ = ⊤
... | ¬⊤ = ⊥
... | ¬¬ ψ = ψ
... | ⊥∨ ψ = ψ
... | ψ ∨⊥ = ψ
... | ⊤∨ ψ = ⊤
... | ψ ∨⊤ = ⊤
... | ⊥∧ ψ = ⊥
... | ψ ∧⊥ = ⊥
... | ⊤∧ ψ = ψ
... | ψ ∧⊤ = ψ
... | ⊥⇒ ψ = ⊤
... | ψ ⇒⊥ = ¬ ψ
... | ⊤⇒ ψ = ψ
... | ψ ⇒⊤ = ⊤
... | ⊥⇔ ψ = ¬ ψ
... | ψ ⇔⊥ = ¬ ψ
... | ⊤⇔ ψ = ψ
... | ψ ⇔⊤ = ψ
... | stop ψ = ψ
```

The second function !ref(simplify) takes care of the recursive structure of the formula in order to apply !ref(simplify1) "deeply"
(no view is used here):

```
simplify ⊥ = ⊥
simplify ⊤ = ⊤
simplify (` p) = ` p
simplify (¬ φ) = simplify1 (¬ simplify φ)
simplify (φ ∨ ψ) = simplify1 (simplify φ ∨ simplify ψ)
simplify (φ ∧ ψ) = simplify1 (simplify φ ∧ simplify ψ)
simplify (φ ⇒ ψ) = simplify1 (simplify φ ⇒ simplify ψ)
simplify (φ ⇔ ψ) = simplify1 (simplify φ ⇔ simplify ψ)
```

!example(#example:simplify)
~~~~~
We can see our simplification procedure in action on some simple examples:

```
_ : simplify (¬ ¬ ¬ ¬ ` p₀) ≡ ` p₀
_ = refl

_ : simplify (¬ (⊤ ∧ ¬ ` p₀)) ≡ ` p₀
_ = refl

_ : simplify (⊤ ∧ ¬ ¬ (¬ ` p₀ ∨ ¬ ¬ ` p₁)) ≡ ¬ ` p₀ ∨ ` p₁
_ = refl
```

Notice how applying simplification deeply in the formula enables further simplification.
~~~~~

## Correctness

We show that the simplification procedure preserves the meaning of the formula:

```
simplify1-sound : ∀ φ →
  ----------------
  simplify1 φ ⟺ φ

simplify-sound : ∀ φ →
  ---------------
  simplify φ ⟺ φ
```

!hide
~~~~
The definition of !ref(simplify1-sound) is by a case analysis based on !ref(simplifyView).
The use of the `--rewriting` option triggers automatic Boolean rewrites in the background
(such as `ff ∨𝔹 b ≡ b`; c.f. [Booleans](../../part0/Booleans)),
which makes the proof straightforward.
~~~~
~~~~
```
simplify1-sound φ ϱ
  with simplifyView φ
... | ¬⊥ = refl
... | ¬⊤ = refl
... | ¬¬ ψ = refl
... | ⊥∨ ψ = refl
... | ψ ∨⊥ = refl
... | ⊤∨ ψ = refl
... | ψ ∨⊤ = refl
... | ⊥∧ ψ = refl
... | ψ ∧⊥ = refl
... | ⊤∧ ψ = refl
... | ψ ∧⊤ = refl
... | ⊥⇒ ψ = refl
... | ψ ⇒⊥ = refl
... | ⊤⇒ ψ = refl
... | ψ ⇒⊤ = refl
... | ⊥⇔ ψ = refl
... | ψ ⇔⊥ = refl
... | ⊤⇔ ψ = refl
... | ψ ⇔⊤ = refl
... | stop ψ = refl
```
~~~~

!hide
~~~~
The definition of !ref(simplify-sound) relies on !ref(simplify1-sound) and is by a routine structural induction.
~~~~
~~~~
```
simplify-sound ⊥ ϱ = refl
simplify-sound ⊤ ϱ = refl
simplify-sound (` p) ϱ = refl
simplify-sound (¬ φ) ϱ
  rewrite simplify1-sound (¬ simplify φ) ϱ |
          simplify-sound φ ϱ = refl
simplify-sound (φ ∨ ψ) ϱ
  rewrite simplify1-sound (simplify φ ∨ simplify ψ) ϱ |
          simplify-sound φ ϱ |
          simplify-sound ψ ϱ = refl
simplify-sound (φ ∧ ψ) ϱ
  rewrite simplify1-sound (simplify φ ∧ simplify ψ) ϱ |
          simplify-sound φ ϱ |
          simplify-sound ψ ϱ = refl
simplify-sound (φ ⇒ ψ) ϱ
  rewrite simplify1-sound (simplify φ ⇒ simplify ψ) ϱ |
          simplify-sound φ ϱ |
          simplify-sound ψ ϱ = refl
simplify-sound (φ ⇔ ψ) ϱ
  rewrite simplify1-sound (simplify φ ⇔ simplify ψ) ϱ |
          simplify-sound φ ϱ |
          simplify-sound ψ ϱ = refl
```
~~~~

<!--

## Structure

We prove that !ref(simplify) produces a formula not containing the zero-ary connectives !ref(Formula)(⊥) and !ref(Formula)(⊤), unless this is all that there is in the formula.

-- data No[⊤,⊥] : Formula → Set where
--   `_ : ∀ p → No[⊤,⊥] (` p)
--   ¬_ : No[⊤,⊥] φ → No[⊤,⊥] (¬ φ)
--   _∨_ : No[⊤,⊥] φ → No[⊤,⊥] ψ → No[⊤,⊥] (φ ∨ ψ)
--   _∧_ : No[⊤,⊥] φ → No[⊤,⊥] ψ → No[⊤,⊥] (φ ∧ ψ)
--   _⇒_ : No[⊤,⊥] φ → No[⊤,⊥] ψ → No[⊤,⊥] (φ ⇒ ψ)
--   _⇔_ : No[⊤,⊥] φ → No[⊤,⊥] ψ → No[⊤,⊥] (φ ⇔ ψ)

-- data Simplified : Formula → Set where
--   ⊥ : Simplified ⊥
--   ⊤ : Simplified ⊤
--   no-⊤⊥ : No[⊤,⊥] φ → Simplified φ

-- simplified1-¬ : Simplified φ → Simplified (simplify1 (¬ φ))
-- simplified1-¬ {φ} simp-φ = {!!}

-- simplified1-∨ : Simplified φ → Simplified ψ → Simplified (simplify1 (φ ∨ ψ))
-- simplified1-∨ {φ} {ψ} simp-φ simp-ψ
--   with simplifyView (φ ∨ ψ)
-- ... | ⊥∨ .ψ = simp-ψ
-- ... | .φ ∨⊥ = simp-φ
-- ... | ⊤∨ .ψ = simp-φ
-- ... | .φ ∨⊤ = simp-ψ
-- ... | stop .(φ ∨ ψ) = {! !} -- no information here, need to improve the view to be more precise

-- simplified : ∀ φ → Simplified (simplify φ)
-- simplified ⊥ = ⊥
-- simplified ⊤ = ⊤
-- simplified (` p) = no-⊤⊥ (` p)
-- simplified (¬ φ) = simplified1-¬ (simplified φ) 
-- simplified (φ ∨ ψ) = simplified1-∨ (simplified φ) (simplified ψ)
-- simplified (φ ∧ φ₂) = {!!}
-- simplified (φ ⇒ φ₂) = {!!}
-- simplified (φ ⇔ φ₂) = {!!}

-->

# Duality

The connectives in the fragment `{⊥,⊤,¬,∨,∧}` have a fundamental duality:

* The two constants !remoteRef(part1)(Semantics)(Formula)(⊥) and !remoteRef(part1)(Semantics)(Formula)(⊤) are dual to each other.
* Negation !remoteRef(part1)(Semantics)(Formula)(¬_) is dual to itself.
* Conjunction !remoteRef(part1)(Semantics)(Formula)(_∧_) and disjunction !remoteRef(part1)(Semantics)(Formula)(_∨_) are dual to each other.

This captured by the following definition,
which given a formula `φ` constructs its *dual* `φ ⁻`
by recursively swaping each constructor with its dual:

```
infix 200 _⁻
_⁻ : Formula → Formula
⊥ ⁻ = ⊤
⊤ ⁻ = ⊥
(` p) ⁻ = ` p
(¬ φ) ⁻ = ¬ φ ⁻
(φ ∧ ψ) ⁻ = φ ⁻ ∨ ψ ⁻
(φ ∨ ψ) ⁻ = φ ⁻ ∧ ψ ⁻
φ ⁻ = φ
```

(In the last catch-all case we do not do anything,
since we will not apply dualisation outside the `{⊥,⊤,¬,∨,∧}` fragment.)

!example(#example:dualisation)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

```
_ : ∀ {φ ψ} → (φ ∨ ¬ ψ) ⁻ ≡ φ ⁻ ∧ ¬ ψ ⁻
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the proofs that follow,
we want to capture the fact that a formula does not contain implications or bi-implications.
To this end, we define the following view:

```
data Formula[⊥,⊤,¬,∨,∧] : Formula → Set where
  ⊥ : Formula[⊥,⊤,¬,∨,∧] ⊥
  ⊤ : Formula[⊥,⊤,¬,∨,∧] ⊤
  `_ : ∀ p → Formula[⊥,⊤,¬,∨,∧] (` p)
  ¬_ : ∀ {φ} → Formula[⊥,⊤,¬,∨,∧] φ → Formula[⊥,⊤,¬,∨,∧] (¬ φ)
  _∨_ : ∀ {φ ψ} → Formula[⊥,⊤,¬,∨,∧] φ → Formula[⊥,⊤,¬,∨,∧] ψ
    → Formula[⊥,⊤,¬,∨,∧] (φ ∨ ψ)
  _∧_ : ∀ {φ ψ} → Formula[⊥,⊤,¬,∨,∧] φ → Formula[⊥,⊤,¬,∨,∧] ψ
    → Formula[⊥,⊤,¬,∨,∧] (φ ∧ ψ)
```

Notice that this view is *recursive*,
since we need to have views of subformulas in order to construct views of compound formulas.
We will not actually compute this view here,
but just use it as an additional assumption to the properties in the rest of the section
in order to exclude from consideration formulas involving implication or bi-impication.
(We will come back to this view in !chapterRef(part1)(CharacteristicFormulas) as part of functional completeness,
where we will provide a way to compute it; c.f. !remoteRef(part1)(CharacteristicFormulas)(funCompl[⊥,⊤,¬,∨,∧]).)

!exercise(#exercise:dual-involution)
~~~~~~
Show that dualisation is an involutive operator,
in the sense that applying it twice leaves the formula unchanged:

```
dual-involutive :
  Formula[⊥,⊤,¬,∨,∧] φ →
  ----------
  φ ⁻ ⁻  ≡ φ
```

The extra assumption `Formula[⊥,⊤,¬,∨,∧] φ` dispenses us from considering formulas with implication or bi-implication.
~~~~~~
~~~~~~
```
dual-involutive ⊥ = refl
dual-involutive ⊤ = refl
dual-involutive (` p) = refl
dual-involutive (¬ φ)
  rewrite dual-involutive φ = refl
dual-involutive (φ ∧ ψ)
  rewrite dual-involutive φ |
          dual-involutive ψ = refl
dual-involutive (φ ∨ ψ)
  rewrite dual-involutive φ |
          dual-involutive ψ = refl
```
~~~~~~

## Duality lemma

Dualisation satisfies a key semantic property.
For a valuation !ref(ϱ), let `- ϱ` be the *opposite valuation*,
which is obtained by negating the output of !ref(ϱ):

```
-_ : Val → Val
(- ϱ) p = ¬𝔹 ϱ p
```

The fundamental semantic property of dualisation is the following:

!lemma(#lemma:duality)(Duality lemma)
~~~~~~~~~~~~~~~~~~~~
```
duality : ∀ {φ} ϱ →
  Formula[⊥,⊤,¬,∨,∧] φ →
  --------------------------
  ⟦ φ ⁻ ⟧ ϱ ≡ ¬𝔹 ⟦ φ ⟧ (- ϱ)
```
~~~~~~~~~~~~~~~~~~~~

!hide
~~~~~~~~~~~
The proof follows a straightforward structural induction,
relying on de Morgan's laws !remoteRef(part1)(Semantics)(deMorganAnd) and !remoteRef(part1)(Semantics)(deMorganOr) for conjunction, resp., disjunction.
~~~~~~~~~~~
~~~~~~~~~~~
```
duality _ ⊥ = refl
duality _ ⊤ = refl
duality {` p} ϱ (` p)
  with ϱ p
... | tt = refl
... | ff = refl
duality ϱ (¬ φ)
  rewrite duality ϱ φ = refl
duality {φ ∧ ψ} ϱ (view-φ ∧ view-ψ)
  rewrite duality ϱ view-φ |
          duality ϱ view-ψ = sym (deMorganAnd φ ψ (- ϱ))
duality {φ ∨ ψ} ϱ (view-φ ∨ view-ψ)
  rewrite duality ϱ view-φ |
          duality ϱ view-ψ = sym (deMorganOr φ ψ (- ϱ))
```
~~~~~~~~~~~

## Consequences

The next exercises explore some consequences of the duality lemma.

!exercise(#exercise:duality-equivalence-1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Prove that dualisation preserves logical equivalence:

```
duality-equivalence-1 :
  Formula[⊥,⊤,¬,∨,∧] φ →
  Formula[⊥,⊤,¬,∨,∧] ψ →
  φ ⟺ ψ →
  ---------
  φ ⁻ ⟺ ψ ⁻
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
duality-equivalence-1 view-φ view-ψ φ⟺ψ ϱ
  rewrite duality ϱ view-φ |
          duality ϱ view-ψ |
          φ⟺ψ (- ϱ) = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:duality-equivalence-2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
duality-equivalence-2 :
  Formula[⊥,⊤,¬,∨,∧] φ →
  Formula[⊥,⊤,¬,∨,∧] ψ →
  φ ⁻ ⟺ ψ ⁻ →
  -------
  φ ⟺ ψ
```

*Hint:* Use !ref(duality-equivalence-1) and the fact that dualisation preserves `{⊥,⊤,¬,∨,∧}` formulas:

```
dual-preservation :
  Formula[⊥,⊤,¬,∨,∧] φ →
  ------------------------
  Formula[⊥,⊤,¬,∨,∧] (φ ⁻)
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We begin by proving that dualisation preserves `{⊥,⊤,¬,∨,∧}` formulas:

```
dual-preservation ⊥ = ⊤
dual-preservation ⊤ = ⊥
dual-preservation (` p) = ` p
dual-preservation (¬ view-φ)
  = ¬ dual-preservation view-φ
dual-preservation (view-φ ∧ view-ψ)
  = dual-preservation view-φ ∨ dual-preservation view-ψ
dual-preservation (view-φ ∨ view-ψ)
  = dual-preservation view-φ ∧ dual-preservation view-ψ
```

With !ref(dual-preservation) in hand,
we can show !ref(duality-equivalence-2) by appealing to !ref(duality-equivalence-1):

```
duality-equivalence-2 {φ} {ψ} view-φ view-ψ φ⁻⟺ψ⁻ ϱ = ⟦φ⟧ϱ≡⟦ψ⟧ϱ where

  ⟦φ⁻⁻⟧ϱ≡⟦ψ⁻⁻⟧ϱ : ⟦ φ ⁻ ⁻ ⟧ ϱ ≡ ⟦ ψ ⁻ ⁻ ⟧ ϱ
  ⟦φ⁻⁻⟧ϱ≡⟦ψ⁻⁻⟧ϱ
    rewrite duality-equivalence-1
      (dual-preservation view-φ)
      (dual-preservation view-ψ) φ⁻⟺ψ⁻ ϱ = refl

  ⟦φ⟧ϱ≡⟦ψ⟧ϱ : ⟦ φ ⟧ ϱ ≡ ⟦ ψ ⟧ ϱ
  ⟦φ⟧ϱ≡⟦ψ⟧ϱ
    rewrite sym (dual-involutive view-φ) |
            sym (dual-involutive view-ψ) = ⟦φ⁻⁻⟧ϱ≡⟦ψ⁻⁻⟧ϱ
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:duality-tautology)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Show that, if `φ` is a tautology,
then the negation of its dual `¬ φ ⁻` is also a tautology:

```
duality-tautology : ∀ {φ} →
  Formula[⊥,⊤,¬,∨,∧] φ →
  Tautology φ →
  -----------------
  Tautology (¬ φ ⁻)
```

*Hint*: Use the fact that a tautology is logically equivalent to !remoteRef(part1)(Semantics)(Formula)(⊤);
c.f. !remoteRef(part1)(Semantics)(tautology-equivalence).
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
duality-tautology {φ} view-φ tau-φ ϱ = goal tau-φ where
  goal = Tautology φ       {-1-} by⟨ fst (tautology-equivalence φ) ⟩
         φ ⟺ ⊤             {-2-} by⟨ duality-equivalence-1 view-φ ⊤ ⟩
         φ ⁻ ⟺ ¬ ⊤         {-3-} by⟨ congF (φ ⁻) (¬ ⊤) (¬ ` p₀) p₀ ⟩
         ¬ φ ⁻ ⟺ ¬ ¬ ⊤     {-4-} by⟨ flip (trans-⟺ (¬ φ ⁻) (¬ ¬ ⊤) ⊤) ¬¬⊤⟺⊤ ⟩
         ¬ φ ⁻ ⟺ ⊤         {-5-} by⟨ flip (snd (tautology-equivalence (¬ φ ⁻))) ϱ ⟩
         ¬𝔹 ⟦ φ ⁻ ⟧ ϱ ≡ tt QED
```

TODO: provide somewhere an introduction to !remoteRef(part0)(Functions)(_by⟨_⟩_).

We comment on each step of the proof:

1) We begin by applying the left-to-right direction of !remoteRef(part1)(Semantics)(tautology-equivalence).
2) By !ref(duality-equivalence-1) we lift the equivalence to the dual formula `φ ⁻`.
3) By simple reasoning based on the fact that !remoteRef(part1)(Semantics)(_⟺_) is a congruence,
we have that `¬ φ ⁻` is logically equivalent to `¬ ¬ ⊤`
4) Thanks to !remoteRef(part1)(Semantics)(¬¬⊤⟺⊤), `¬ φ ⁻` is logically equivalent to !remoteRef(part1)(Semantics)(Formula)(⊤).
5) The proof is concluded by applying the right-to-left direction of !remoteRef(part1)(Semantics)(tautology-equivalence).
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
