---
title: Characteristic formulas and functional completeness 🚧
---

In this chapter we study characteristic formulas and their application to functionally complete set of connectives.

```
{-# OPTIONS --allow-unsolved-metas  #-}
open import part0.index

module part1.CharacteristicFormulas (n′ : ℕ) where
open import part1.Semantics n′ public
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

that assigns value !remoteRef(part0)(Booleans)(𝔹)(tt) to every proposition,
except for `p₀` and `p₁`.
Under the assumption that there are only three propositions `p₀, p₁, p₂` in the universe,
a characteristic formula for `ϱ₁` is, e.g.,

```
private ψ₁ : Formula
ψ₁ = ¬ ` p₀ ∧ ¬ ` p₁ ∧ ` p₂
```

In order to show `ψ₁ CharFormulaOf ϱ₁`, we use appropriate Boolean inversion properties
to enforce that every valuation `ϱ′` satisfying `ψ₁`
necessarily assigns !remoteRef(part0)(Booleans)(𝔹)(ff) to `p₀, p₁`, and !remoteRef(part0)(Booleans)(𝔹)(tt) to `p₂`.
We then use function extensionality to conclude `ϱ′ ≡ ϱ₁`, as required:

```
ψ₁CharFormulaOfϱ₁ : n ≡ 3 → ψ₁ CharFormulaOf ϱ₁
ψ₁CharFormulaOfϱ₁ refl = refl , goal where

  goal : ∀ ϱ′ → ⟦ ψ₁ ⟧ ϱ′ ≡ tt → ϱ′ ≡ ϱ₁
  goal ϱ′ eval
    with 𝔹conjProp1 (⟦ ¬ ` p₀ ⟧ ϱ′) (⟦ ¬ ` p₁ ∧ ` p₂ ⟧ ϱ′) eval |
         𝔹conjProp1 (⟦ ¬ ` p₁ ⟧ ϱ′) _ (𝔹conjProp2 (⟦ ¬ ` p₀ ⟧ ϱ′) _ eval) |
         𝔹conjProp2 (⟦ ¬ ` p₁ ⟧ ϱ′) _ (𝔹conjProp2 (⟦ ¬ ` p₀ ⟧ ϱ′) _ eval)
  ... | eval1 | eval2 | eval3
    with ¬𝔹-inv (ϱ′ p₀) eval1 |
         ¬𝔹-inv (ϱ′ p₁) eval2
  ... | eval1' | eval2' = extensionality go where

    go : ∀[ p ] ϱ′ p ≡ ϱ₁ p
    go fzero rewrite eval1' = refl 
    go (fsuc fzero) rewrite eval2' =  refl 
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

In the first case (i.e., if `ϱ p` is !remoteRef(part0)(Booleans)(𝔹)(tt))
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
For example in the first case we need to rewrite twice according to the same equality `ϱp≡tt : ϱ p ≡ tt`:
The first rewrite transforms `⟦ 「 p 」 ϱ ⟧ ϱ` into ``⟦ ` p ⟧ ϱ``,
and the second rewrite transforms the latter into !remoteRef(part0)(Booleans)(𝔹)(tt), as required.
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
_ : n ≡ 3 → 〔 ϱ₀ 〕 ≡ ¬ ` p₀ ∧ ¬ ` p₁ ∧ ` p₂
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
  
charFormula-sound ϱ = conjProp2 literals ϱ go where

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

(We open the local module `CharFormula` in order to use the definition of `literals` from `〔_〕`.)s
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
    ∈literals = map-∈ (「_」 ϱ) (findPropName p)
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
In fact, we have already encountered this fragment in !remoteRef(part1)(Semantics)(Formula[⊥,⊤,¬,∨,∧]).

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
f₀ ϱ = foldr (λ b₀ b₁ → b₁ ∧𝔹 ⌞ b₀ ≡? ϱ p₀ ⌟) tt (map ϱ propNames)
```

We can construct the corresponding formula in the special case of three propositional variables
(the application of !ref(simplify) removes some redundant !ref(Formula)(⊤) and !ref(Formula)(⊥) constants):

```
_ : n ≡ 3 → simplify (fun→formula f₀) ≡
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
xor ϱ = foldr (λ b₀ b₁ → ⌞ b₀ ≡? b₁ ⌟) (ϱ p₀) (tail (map ϱ propNames))

_ : n ≡ 3 → simplify (fun→formula xor) ≡
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
Formula[⊥,⊤,¬,∨,∧]-⋀-closed (φ ∷ ε) all = all here
Formula[⊥,⊤,¬,∨,∧]-⋀-closed (φ ∷ φs@(_ ∷ _)) all
  with Formula[⊥,⊤,¬,∨,∧]-⋀-closed φs (λ φ∈φs → all (there φ∈φs))
... | ind = all here ∧ ind 

Formula[⊥,⊤,¬,∨,∧]-⋁-closed : ∀ φs → All Formula[⊥,⊤,¬,∨,∧] φs → Formula[⊥,⊤,¬,∨,∧] (⋁ φs)
Formula[⊥,⊤,¬,∨,∧]-⋁-closed ε all = ⊥
Formula[⊥,⊤,¬,∨,∧]-⋁-closed (φ ∷ ε) all = all here
Formula[⊥,⊤,¬,∨,∧]-⋁-closed (φ ∷ φs@(_ ∷ _)) all
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

We begin by finding the occurrence `findVal ϱ` of `ϱ` in the list of all valuations !ref(vals) and then, knowing that `f ϱ` evaluates to !remoteRef(part0)(Booleans)(𝔹)(tt) by assumption,
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

!remark(#remark:funComplFalseTrueNegAndOr)
~~~~~~~~~~~~
The formula computed by !ref(fun→formula) enjoys stronger structural properties than being in the `{∨, ∧, ¬, ⊤, ⊥}` fragment.
In fact, it always produces formulas of the form $$\bigvee_i \bigwedge_j l_{i,j}$$
where $l_{i,j}$ is a literal. Such formulas are said to be in *disjunctive normal form* (DNF).
We will come back to DNF formulas in !chapterRef(part1)(NormalForms) where we will study this and other normal forms.

Regarding efficiency, !ref(fun→formula) iterates over all valuations
and thus invariably produces formulas of exponential size $\Theta(2^n)$.
This will be (partially) addressed also in !chapterRef(part1)(NormalForms) with a syntactic construction.
~~~~~~~~~~~~

## Fragment `{∨, ∧, ¬}` {#sec:fragmentOrAndNeg}

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

TODO: Explain that `remove⊥⊤` is written using the "implicit verification" approach.
First occurrence of this in part 1.

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

## Fragment `{⊥, ⊤, ∨, ∧}` {#sec:monotone-fragment}

At this point one may get the impression that most set of connectives are semantically complete.
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
Formula[⊥,⊤,∨,∧]-⋀-closed (φ ∷ ε) all = all here
Formula[⊥,⊤,∨,∧]-⋀-closed (φ ∷ φs@(_ ∷ _)) all
  with Formula[⊥,⊤,∨,∧]-⋀-closed φs (λ φ∈φs → all (there φ∈φs))
... | ind = all here ∧ ind

Formula[⊥,⊤,∨,∧]-⋁-closed ε all = ⊥
Formula[⊥,⊤,∨,∧]-⋁-closed (φ ∷ ε) all = all here
Formula[⊥,⊤,∨,∧]-⋁-closed (φ ∷ φs@(_ ∷ _)) all
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
Intuitively, a Boolean function is monotone iff flipping one input from !remoteRef(part0)(Booleans)(𝔹)(ff) to !remoteRef(part0)(Booleans)(𝔹)(tt) can only increase the output.
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

## Fragment `{⊤, ∨, ∧, ⇒, ⇔}` {#section:big-incomplete-fragment}

Let's now consider all standard connectives,
except the "negative" connectives !remoteRef(part1)(Semantics)(Formula)(⊥) and !remoteRef(part1)(Semantics)(Formula)(¬_):

```
data Formula[⊤,∨,∧,⇒,⇔] : Formula → Set where
  ⊤ : Formula[⊤,∨,∧,⇒,⇔] ⊤
  `_ : ∀ p → Formula[⊤,∨,∧,⇒,⇔] (` p)
  _∧_ : ∀ {φ ψ} → Formula[⊤,∨,∧,⇒,⇔] φ → Formula[⊤,∨,∧,⇒,⇔] ψ →
    Formula[⊤,∨,∧,⇒,⇔] (φ ∧ ψ)
  _∨_ : ∀ {φ ψ} → Formula[⊤,∨,∧,⇒,⇔] φ → Formula[⊤,∨,∧,⇒,⇔] ψ →
    Formula[⊤,∨,∧,⇒,⇔] (φ ∨ ψ)
  _⇒_ : ∀ {φ ψ} → Formula[⊤,∨,∧,⇒,⇔] φ → Formula[⊤,∨,∧,⇒,⇔] ψ →
    Formula[⊤,∨,∧,⇒,⇔] (φ ⇒ ψ)
  _⇔_ : ∀ {φ ψ} → Formula[⊤,∨,∧,⇒,⇔] φ → Formula[⊤,∨,∧,⇒,⇔] ψ →
    Formula[⊤,∨,∧,⇒,⇔] (φ ⇔ ψ)
```

!exercise(#exercise:positive-connective)(The `{⊤, ∨, ∧, ⇒, ⇔}` fragment)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Is the set of "positive" connectives `{⊤, ∨, ∧, ⇒, ⇔}` semantically complete?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The set of positive connectives is not semantically complete.
To see this, we will prove the following stronger property:

```
Formula[⊤,∨,∧,⇒,⇔]-tt : ∀ φ →
  Formula[⊤,∨,∧,⇒,⇔] φ →
  --------------
  ⟦ φ ⟧ ϱtt ≡ tt
```

In other words, formulas with only positive connectives necessarily evaluate to !remoteRef(part0)(Booleans)(Booleans)(tt) under the constantly true valuation !remoteRef(part1)(Semantics)(ϱtt).
After realising this, the proof is a straightforward structural induction:

```
Formula[⊤,∨,∧,⇒,⇔]-tt ⊤ ⊤ = refl
Formula[⊤,∨,∧,⇒,⇔]-tt (` p) (` p) = refl
Formula[⊤,∨,∧,⇒,⇔]-tt (φ ∧ ψ) (view-φ ∧ view-ψ)
  rewrite Formula[⊤,∨,∧,⇒,⇔]-tt φ view-φ |
          Formula[⊤,∨,∧,⇒,⇔]-tt ψ view-ψ = refl
Formula[⊤,∨,∧,⇒,⇔]-tt (φ ∨ ψ) (view-φ ∨ view-ψ)
  rewrite Formula[⊤,∨,∧,⇒,⇔]-tt φ view-φ |
          Formula[⊤,∨,∧,⇒,⇔]-tt ψ view-ψ = refl
Formula[⊤,∨,∧,⇒,⇔]-tt (φ ⇒ ψ) (view-φ ⇒ view-ψ)
  rewrite Formula[⊤,∨,∧,⇒,⇔]-tt φ view-φ |
          Formula[⊤,∨,∧,⇒,⇔]-tt ψ view-ψ = refl
Formula[⊤,∨,∧,⇒,⇔]-tt (φ ⇔ ψ) (view-φ ⇔ view-ψ)
  rewrite Formula[⊤,∨,∧,⇒,⇔]-tt φ view-φ |
          Formula[⊤,∨,∧,⇒,⇔]-tt ψ view-ψ = refl
```

With this property in hand, we can show that the positive fragment is not functionally complete.

```
~FunCompl[⊤,∨,∧,⇒,⇔] : ~ FunctionallyComplete Formula[⊤,∨,∧,⇒,⇔]
~FunCompl[⊤,∨,∧,⇒,⇔] funcompl
```

By the assumption, we can represent every Boolean function with a positive formula,
and in particular the function which is constantly false,

```
  with funcompl (const ff)
... | φ , view-φ , ⟦φ⟧≡ff
```

however, positive formulas necessarily evaluate to true under the all-true valuation, leading to a contradiction:

```
  with Formula[⊤,∨,∧,⇒,⇔]-tt φ view-φ 
... | ⟦φ⟧ϱtt≡tt rewrite ⟦φ⟧≡ff = ff≢tt ⟦φ⟧ϱtt≡tt 
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

## Fragment `{⇑}` -- Sheffer's stroke {#Sheffer}

In this section we consider whether it is possible for a *single* connective to be semantically complete w.r.t. all Boolean functions.
Clearly the connective cannot be unary,
since formulas built from a single unary connective can only depend on the Boolean value of one fixed input variable.
Thus the connective must be binary. There are $2^{2^2} = 16$ Boolean functions of two arguments.
By !refSection(#section:monotone-fragment) it cannot be monotone.
This already excludes $D(2) = 6$ functions,
where $D(n)$ is the $n$-th *Dedekind number* [@Dedekind:1897] which counts the number of Boolean functions of $n$ arguments (c.f. [OEIS A000372](https://oeis.org/A000372) for its first 9 known values).
Even more strongly, by !refSection(#section:big-incomplete-fragment) it must map !remoteRef(part1)(Semantics)(ϱff) to true,
and by a symmetric argument it must map !remoteRef(part1)(Semantics)(ϱtt) to false.
This means that we can only choose the output for the "intermediate inputs" `(ff , tt)` and `( tt , ff )`,
thus there are only four options left:

```
g₀ g₁ g₂ g₃  : 𝔹 × 𝔹 → 𝔹
g₀ = const tt
  [ ff , ff ↦ tt ]
  [ ff , tt ↦ ff ]
  [ tt , ff ↦ ff ]
  [ tt , tt ↦ ff ]

g₁ = const tt
  [ ff , ff ↦ tt ]
  [ ff , tt ↦ ff ]
  [ tt , ff ↦ tt ]
  [ tt , tt ↦ ff ]

g₂ = const tt
  [ ff , ff ↦ tt ]
  [ ff , tt ↦ tt ]
  [ tt , ff ↦ ff ]
  [ tt , tt ↦ ff ]

g₃ = const tt
  [ ff , ff ↦ tt ]
  [ ff , tt ↦ tt ]
  [ tt , ff ↦ tt ]
  [ tt , tt ↦ ff ]
```

The two functions !ref(g₁) and !ref(g₂) can be discarded since they compute just the negation of the second, resp., first argument,
and thus do not depend on both arguments.
Each of the two remaining functions !ref(g₀) and !ref(g₃) is suitable as a basis.
For this reason, they deserve a name:

```
_nor𝔹_ _nand𝔹_ : 𝔹 → 𝔹 → 𝔹
b₀ nor𝔹 b₁ = ¬𝔹 (b₀ ∨𝔹 b₁)  -- g₀
b₀ nand𝔹 b₁ = ¬𝔹 (b₀ ∧𝔹 b₁) -- g₃
```

Sheffer showed that !ref(_nor𝔹_) can be taken as a basis and he denotes it with a *stroke* (vertical bar) `_|_` [Theorem 1, @Sheffer:AMS:1913].
We show the analogous result for !ref(_nand𝔹_),
and in honour of Sheffer we will call it the *Sheffer's stroke*:

```
_⇑_ : Formula → Formula → Formula
φ ⇑ ψ = ¬ (φ ∧ ψ)
```

(Since we cannot add a new connective to formulas,
we have to define the stroke in terms of existing connectives.)
The corresponding class of formulas is defined as follows:

```
data Formula[⇑] : Formula → Set where
  `_ : ∀ p → Formula[⇑] (` p)
  _nand_ : ∀ {φ ψ} → Formula[⇑] φ → Formula[⇑] ψ → Formula[⇑] (φ ⇑ ψ)
```

Unfortunately, since !ref(_⇑_) is not a constructor,
we cannot homonymously name the corresponding constructor in !ref(Formula[⇑]),
hence !ref(Formula[⇑])(_nand_). 

!exercise(#exercise:sheffer-fun)
~~~~~~~~~~~~~~~
Show how to encode negation and conjunction in terms of Sheffer's stroke:

```
[∧,¬]→[⇑] : ∀ {φ} → Formula[¬∧] φ → Formula
```
~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~
```
[∧,¬]→[⇑] (` p) = ` p

[∧,¬]→[⇑] (¬ viewφ)
  with [∧,¬]→[⇑] viewφ
... | ψ = ψ ⇑ ψ

[∧,¬]→[⇑] (viewφ ∧ viewψ)
  with [∧,¬]→[⇑] viewφ |
       [∧,¬]→[⇑] viewψ
... | φ' | ψ' = let ξ = φ' ⇑ ψ' in ξ ⇑ ξ
```
~~~~~~~~~~~~~~~

!exercise(#exercise:sheffer-fragment)
~~~~~~~~~~~~~~~
Show that the encoding from !refExercise(#exercise:sheffer-fun) produces a formula in !ref(Formula[⇑]):

```
[∧,¬]→[⇑]-fragment : ∀ {φ} →
  (viewφ : Formula[¬∧] φ) →
  -----------------------------
  Formula[⇑] ([∧,¬]→[⇑] viewφ)
```
~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~
```
[∧,¬]→[⇑]-fragment (` p) = ` p

[∧,¬]→[⇑]-fragment (¬ viewφ)
  with [∧,¬]→[⇑]-fragment viewφ
  
... | viewψ = viewψ nand viewψ
[∧,¬]→[⇑]-fragment (viewφ ∧ viewψ)
  with [∧,¬]→[⇑]-fragment viewφ |
       [∧,¬]→[⇑]-fragment viewψ
... | viewφ' | viewψ' = let viewξ = viewφ' nand viewψ' in
                        viewξ nand viewξ
```
~~~~~~~~~~~~~~~

!exercise(#exercise:sheffer-sound)
~~~~~~~~~~~~~~~
Show that the encoding from !refExercise(#exercise:sheffer-fun) is sound:

```
[∧,¬]→[⇑]-sound : ∀ {φ} →
  (viewφ : Formula[¬∧] φ) →
  ---------------------
  φ ⟺ [∧,¬]→[⇑] viewφ
```
~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~
```
[∧,¬]→[⇑]-sound (` p) ϱ = refl

[∧,¬]→[⇑]-sound (¬ viewφ) ϱ
  rewrite [∧,¬]→[⇑]-sound viewφ ϱ
  with ⟦ [∧,¬]→[⇑] viewφ ⟧ ϱ
... | tt = refl
... | ff = refl

[∧,¬]→[⇑]-sound (viewφ ∧ viewψ) ϱ
  rewrite [∧,¬]→[⇑]-sound viewφ ϱ |
          [∧,¬]→[⇑]-sound viewψ ϱ
  with ⟦ [∧,¬]→[⇑] viewφ ⟧ ϱ |
       ⟦ [∧,¬]→[⇑] viewψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl
```
~~~~~~~~~~~~~~~
