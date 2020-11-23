---
title: "Normal forms 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas --rewriting --confluence-check #-}
open import part0.index

module part1.NormalForms (n : ℕ) where
open import part1.Semantics n hiding (∅)
 
private
  variable
    φ ψ ξ : Formula
```

In this chapter we study normal forms for classical propositional logic, namely

* [weak negation normal form (WNNF)](#WNNF),
* [negation normal form (NNF)](#NNF),
* [disjunctive normal form (DNF)](#DNF), and its dual
* [conjunctive normal form (CNF)](#CNF).


# Weak negation normal form {#WNNF}

A *literal* is either a propositional variable `p` (positive literal)
or a negation `¬ p` thereof (negative literal).
A formula is in *weak negation normal form* (WNNF) if negation can appear only in literals,
i.e., in front of propositional variables:

```
data WNNF : Formula → Set where
  ⊤ : WNNF ⊤
  ⊥ : WNNF ⊥
  `_ : (p : PropName) → WNNF (` p)
  ¬`_ : (p : PropName) → WNNF (¬ ` p)
  _∧_ : WNNF φ → WNNF ψ → WNNF (φ ∧ ψ)
  _∨_ : WNNF φ → WNNF ψ → WNNF (φ ∨ ψ)
  _⇒_ : WNNF φ → WNNF ψ → WNNF (φ ⇒ ψ)
  _⇔_ : WNNF φ → WNNF ψ → WNNF (φ ⇔ ψ)

infix 100 `_
infix 99 ¬`_
infixr 98 _∧_
infixr 97 _∨_ _⇒_
infixr 96 _⇔_
```

In this section we show that every formula can be transformed to a logically equivalent formula in WNNF.
This is a preparatory step towards the stronger [NNF](#NNF).

Given a formula `φ`, we can decide whether it is in WNNF or not:

```
WNNF? : ∀ φ → Dec (WNNF φ)
```

!hide
~~~
The proof works by inspecting `φ` sufficiently deeply.
~~~
~~~
```
WNNF? ⊥ = yes ⊥
WNNF? ⊤ = yes ⊤
WNNF? (` p) = yes (` p)

WNNF? (¬ ⊥) = no λ ()
WNNF? (¬ ⊤) = no λ ()
WNNF? (¬ (` p)) = yes (¬` p)
WNNF? (¬ (¬ _)) = no λ ()
WNNF? (¬ (_ ∨ _)) = no λ ()
WNNF? (¬ (_ ∧ _)) = no λ ()
WNNF? (¬ (_ ⇒ _)) = no λ ()
WNNF? (¬ (_ ⇔ _)) = no λ ()

WNNF? (φ ∨ ψ)
  with WNNF? φ |
       WNNF? ψ
... | yes wnnfφ | yes wnnfψ = yes (wnnfφ ∨ wnnfψ)
... | no ¬wnnfφ | _ = no λ{ (wnnfφ ∨ _) → ¬wnnfφ wnnfφ}
... | _ | no ¬wnnfψ = no λ{ (_ ∨ wnnfψ) → ¬wnnfψ wnnfψ}

WNNF? (φ ∧ ψ)
  with WNNF? φ |
       WNNF? ψ
... | yes wnnfφ | yes wnnfψ = yes (wnnfφ ∧ wnnfψ)
... | no ¬wnnfφ | _ = no λ{ (wnnfφ ∧ _) → ¬wnnfφ wnnfφ}
... | _ | no ¬wnnfψ = no λ{ (_ ∧ wnnfψ) → ¬wnnfψ wnnfψ}

WNNF? (φ ⇒ ψ)
  with WNNF? φ |
       WNNF? ψ
... | yes wnnfφ | yes wnnfψ = yes (wnnfφ ⇒ wnnfψ)
... | no ¬wnnfφ | _ = no λ{ (wnnfφ ⇒ _) → ¬wnnfφ wnnfφ}
... | _ | no ¬wnnfψ = no λ{ (_ ⇒ wnnfψ) → ¬wnnfψ wnnfψ}

WNNF? (φ ⇔ ψ)
  with WNNF? φ |
       WNNF? ψ
... | yes wnnfφ | yes wnnfψ = yes (wnnfφ ⇔ wnnfψ)
... | no ¬wnnfφ | _ = no λ{ (wnnfφ ⇔ _) → ¬wnnfφ wnnfφ}
... | _ | no ¬wnnfψ = no λ{ (_ ⇔ wnnfψ) → ¬wnnfψ wnnfψ}

```
~~~

```
ψ₀ ψ₁ ψ₂ ψ₃ ψ₄ ψ₅ ψ₇ ψ₈ : Formula
```

::::::::::::: {.inlinecode}

For instance, the formulas
```
ψ₀ = ⊤
```
,
```
ψ₁ = ¬ ` p₀ ∨ ` p₁
```
, and
```
ψ₂ = ¬ ` p₀ ⇒ (` p₁ ⇔ ¬ ` p₂)
```
are in WNNF, while the formulas
```
ψ₃ = ¬ ⊤
```
,
```
ψ₄ = ¬ ¬ ` p₀
```
, and
```
ψ₅ = ¬ (` p₀ ∨ ` p₁)
```
are not in WNNF (negation not in front of a propositional variable),
which we can automatically check thanks to !ref(WNNF?):

:::::::::::::

```
_ : All? WNNF? ([ ψ₀ ψ₁ ψ₂ ]) ×? All? (~?_ ∘ WNNF?) ([ ψ₃ ψ₄ ψ₅ ]) ≡ yes _
_ = refl
```

## Transformation

The transformation of a formula to WNNF operates by "pushing inside" negations.
This is achieved by the function

```
wnnf : Formula → Formula
```

which is defined as follows:

* In the atomic cases the formula is unchanged:

```
wnnf ⊥ = ⊥
wnnf ⊤ = ⊤
wnnf (` p) = ` p
```

* In the case of binary connectives we just proceed recursively on the subformulas:

```
wnnf (φ ∨ ψ) = wnnf φ ∨ wnnf ψ
wnnf (φ ∧ ψ) = wnnf φ ∧ wnnf ψ
wnnf (φ ⇒ ψ) = wnnf φ ⇒ wnnf ψ
wnnf (φ ⇔ ψ) = wnnf φ ⇔ wnnf ψ
```

* In the case of a negation, we push it inside.
If it is in front of the constants !remoteRef(part1)(Semantics)(Formula)(⊥) and !remoteRef(part1)(Semantics)(Formula)(⊥),
then we just flip it to the other constant:

```
wnnf (¬ ⊥) = ⊤
wnnf (¬ ⊤) = ⊥
```

* If it is in front of a propositional variable,
then we leave it unchanged:

```
wnnf (¬ ` p) = ¬ ` p
```

* Double negations are just removed (thanks to the law of double negation):
  
```
wnnf (¬ ¬ φ) = wnnf φ
```

* If negation is in front of a binary connective,
then we push it inside according to the corresponding de Morgan's law:
  
```
wnnf (¬ (φ ∨ ψ)) = wnnf (¬ φ) ∧ wnnf (¬ ψ)
wnnf (¬ (φ ∧ ψ)) = wnnf (¬ φ) ∨ wnnf (¬ ψ)
wnnf (¬ (φ ⇒ ψ)) = wnnf φ ∧ wnnf (¬ ψ)
wnnf (¬ (φ ⇔ ψ)) = wnnf φ ⇔ wnnf (¬ ψ)
```

!hide
~~~~~~~
<div class="inlinecode"> For example, the WNNF of
```
ψ₇ = ¬ ¬ (` p₀ ⇒ ¬ (` p₁ ∧ ` p₂))
```
is
```
ψ₈ = ` p₀ ⇒ ¬ ` p₁ ∨ ¬ ` p₂
```
as we can automatically check. </div>
~~~~~~~
~~~~~~~
```
_ : wnnf ψ₇ ≡ ψ₈
_ = refl 
```
~~~~~~~

## Correctness

Now that we have a tentative definition of a function !ref(wnnf) purportedly transforming a formula to an equivalent one in WNNF,
we have to prove that this is the case.
There are two things that we need to prove.
First, we need to prove that `wnnf φ` is indeed in WNNF,
and second that it is logically equivalent to `φ`.

### Structure

!hide
~~~~~~~~~
```
wnnf-WNNF : ∀ φ → WNNF (wnnf φ)
```

The proof that `wnnf φ` is in WNNF is by a customary structural induction,
where in the case `φ = ¬ (` p)` the !ref(WNNF) given by the constructor `` ¬` p ``
(no space between `¬` and the following backtick character).
~~~~~~~~~
~~~~~~~~~
```
wnnf-WNNF ⊥ = ⊥
wnnf-WNNF ⊤ = ⊤
wnnf-WNNF (` p) = ` p
wnnf-WNNF (¬ ⊥) = ⊤
wnnf-WNNF (¬ ⊤) = ⊥
wnnf-WNNF (¬ (` p)) = ¬` p
wnnf-WNNF (¬ (¬ φ)) = wnnf-WNNF φ
wnnf-WNNF (¬ (φ ∨ ψ)) = wnnf-WNNF (¬ φ) ∧ wnnf-WNNF (¬ ψ)
wnnf-WNNF (¬ (φ ∧ ψ)) = wnnf-WNNF (¬ φ) ∨ wnnf-WNNF (¬ ψ)
wnnf-WNNF (¬ (φ ⇒ ψ)) = wnnf-WNNF φ ∧ wnnf-WNNF (¬ ψ)
wnnf-WNNF (¬ (φ ⇔ ψ)) = wnnf-WNNF φ ⇔ wnnf-WNNF (¬ ψ)
wnnf-WNNF (φ ∨ ψ) = wnnf-WNNF φ ∨ wnnf-WNNF ψ
wnnf-WNNF (φ ∧ ψ) = wnnf-WNNF φ ∧ wnnf-WNNF ψ
wnnf-WNNF (φ ⇒ ψ) = wnnf-WNNF φ ⇒ wnnf-WNNF ψ
wnnf-WNNF (φ ⇔ ψ) = wnnf-WNNF φ ⇔ wnnf-WNNF ψ
```
~~~~~~~~~

### Soundness

The proof of soundness is conceptually simple and it is based on the double negation and de Morgan's laws.
The only difficulty is posed by the termination checker.

The most immediate way to prove soundness would be to mimic the recursive structure of !ref(wnnf) as follows:

```
{-# TERMINATING #-}
wnnf-sound' : ∀ φ → φ ⟺ wnnf φ

wnnf-sound' ⊥ ϱ = refl
wnnf-sound' ⊤ ϱ = refl
wnnf-sound' (` p) ϱ = refl
wnnf-sound' (¬ ⊥) ϱ = refl
wnnf-sound' (¬ ⊤) ϱ = refl
wnnf-sound' (φ ∨ ψ) ϱ
  rewrite wnnf-sound' φ ϱ |
          wnnf-sound' ψ ϱ = refl
          
wnnf-sound' (φ ∧ ψ) ϱ
  rewrite wnnf-sound' φ ϱ |
          wnnf-sound' ψ ϱ = refl
          
wnnf-sound' (φ ⇒ ψ) ϱ
  rewrite wnnf-sound' φ ϱ |
          wnnf-sound' ψ ϱ = refl
          
wnnf-sound' (φ ⇔ ψ) ϱ
  rewrite wnnf-sound' φ ϱ |
          wnnf-sound' ψ ϱ = refl
          
wnnf-sound' (¬ (` p)) ϱ = refl
wnnf-sound' (¬ (¬ φ)) ϱ
  rewrite doubleNegationLaw φ ϱ |
          wnnf-sound' φ ϱ = refl
  
wnnf-sound' (¬ (φ ∨ ψ)) ϱ
   rewrite deMorganOr φ ψ ϱ |
           wnnf-sound' (¬ φ) ϱ |
           wnnf-sound' (¬ ψ) ϱ = refl -- termination issue (*)
           
wnnf-sound' (¬ (φ ∧ ψ)) ϱ
   rewrite deMorganAnd φ ψ ϱ |
           wnnf-sound' (¬ φ) ϱ |
           wnnf-sound' (¬ ψ) ϱ = refl

wnnf-sound' (¬ (φ ⇒ ψ)) ϱ
   rewrite deMorganImplies φ ψ ϱ |
           wnnf-sound' φ ϱ |
           wnnf-sound' (¬ ψ) ϱ = refl

wnnf-sound' (¬ (φ ⇔ ψ)) ϱ
   rewrite deMorganIff-right φ ψ ϱ |
           wnnf-sound' φ ϱ |
           wnnf-sound' (¬ ψ) ϱ = refl
```

The `TERMINATING` pragma instructs Agda to accept this definition even if it is not proved terminating by the termination checker.
(In this way we do not need to comment out the code.)
This can be verified by commenting out the pragma,
whereby the termination checker will complain about the recursive invocation marked by `(*)` above.
It is surprising that the termination checker cannot establish that !ref(wnnf-sound') is terminating (which indeed it is),
since it has the same recursive structure as !ref(wnnf), which is established terminating.

We need to find a way to convince the termination checker.
A simple work-around with negligible notational overhead  is to split the soundness proof in two parts:

```
wnnf-sound : ∀ φ → φ ⟺ wnnf φ
wnnf¬-sound : ∀ φ → ¬ φ ⟺ wnnf (¬ φ)
```

where the second part takes care of negated formulas.
With this "division of duties" approach,
we can comfortably write the following mutually recursive definitions:

```
wnnf-sound ⊥ ϱ = refl
wnnf-sound ⊤ ϱ = refl
wnnf-sound (` p) ϱ = refl
wnnf-sound (¬ φ) = wnnf¬-sound φ
wnnf-sound (φ ∨ ψ) ϱ
  rewrite wnnf-sound φ ϱ |
          wnnf-sound ψ ϱ = refl
wnnf-sound (φ ∧ ψ) ϱ
  rewrite wnnf-sound φ ϱ |
          wnnf-sound ψ ϱ = refl
wnnf-sound (φ ⇒ ψ) ϱ
  rewrite wnnf-sound φ ϱ |
          wnnf-sound ψ ϱ = refl
wnnf-sound (φ ⇔ ψ) ϱ
  rewrite wnnf-sound φ ϱ |
          wnnf-sound ψ ϱ = refl
```

and

```
wnnf¬-sound ⊥ ϱ = refl
wnnf¬-sound ⊤ ϱ = refl
wnnf¬-sound (` p) ϱ = refl
wnnf¬-sound (¬ φ) ϱ 
  rewrite doubleNegationLaw φ ϱ |
          wnnf-sound φ ϱ = refl
  
wnnf¬-sound (φ ∨ ψ) ϱ
  rewrite deMorganOr φ ψ ϱ |
          wnnf¬-sound φ ϱ |
          wnnf¬-sound ψ ϱ = refl
          
wnnf¬-sound (φ ∧ ψ) ϱ
  rewrite deMorganAnd φ ψ ϱ |
          wnnf¬-sound φ ϱ |
          wnnf¬-sound ψ ϱ = refl

wnnf¬-sound (φ ⇒ ψ) ϱ
  rewrite deMorganImplies φ ψ ϱ |
          wnnf-sound φ ϱ |
          wnnf¬-sound ψ ϱ = refl

wnnf¬-sound (φ ⇔ ψ) ϱ
  rewrite deMorganIff-right φ ψ ϱ |
          wnnf-sound φ ϱ |
          wnnf¬-sound ψ ϱ = refl
```

## Internal verification

An alternative approach is to the define the WNNF transformation and its correctness proof as a single recursive definition:

```
wnnf′ : ∀[ φ ] ∃[ ψ ] WNNF ψ × φ ⟺ ψ
```

!hide
~~~~
This has the advantage of solving the termination problem highlighted above.
One disadvantage is that in contexts where we need just the WNNF formula,
but not its correctness proof,
we cannot write just `wnnf φ`, but we would need to write the less transparent `dfst (wnnf' φ)`.
For this reason, in this section we have preferred an approach where the definition of WNNF and its correctness proof are given separately,
however it is interesting to compare it to the case where they are given together.
This style of programming is sometimes called *internal verification*.
~~~~
~~~~
```
wnnf′ ⊥ = ⊥ , ⊥ , λ ϱ → refl
wnnf′ ⊤ = ⊤ , ⊤ , λ ϱ → refl
wnnf′ (` p) = ` p , ` p , λ ϱ → refl
wnnf′ (¬ ⊥) = ⊤ , ⊤ , λ ϱ → refl
wnnf′ (¬ ⊤) = ⊥ , ⊥ , λ ϱ → refl
wnnf′ (¬ ` p) = ¬ ` p , ¬` p , λ ϱ → refl

wnnf′ (¬ ¬ φ) with wnnf′ φ
... | ψ , WNNFψ , φ⟺ψ = ψ , WNNFψ , correctness where

  correctness : ¬ ¬ φ ⟺ ψ
  correctness ϱ rewrite doubleNegationLaw φ ϱ |
                        φ⟺ψ ϱ = refl

wnnf′ (¬ (φ₀ ∨ φ₁)) with wnnf′ (¬ φ₀) | wnnf′ (¬ φ₁)
... | ψ₀ , WNNFψ₀ , φ₀⟺ψ₀
    | ψ₁ , WNNFψ₁ , φ₁⟺ψ₁ = ψ₀ ∧ ψ₁ , WNNFψ₀ ∧ WNNFψ₁ , correctness where

  correctness : ¬ (φ₀ ∨ φ₁) ⟺ ψ₀ ∧ ψ₁
  correctness ϱ rewrite deMorganOr φ₀ φ₁ ϱ |
                        φ₀⟺ψ₀ ϱ |
                        φ₁⟺ψ₁ ϱ = refl

wnnf′ (¬ (φ₀ ∧ φ₁)) with wnnf′ (¬ φ₀) | wnnf′ (¬ φ₁)
... | ψ₀ , WNNFψ₀ , φ₀⟺ψ₀
    | ψ₁ , WNNFψ₁ , φ₁⟺ψ₁ = ψ₀ ∨ ψ₁ , WNNFψ₀ ∨ WNNFψ₁ , correctness where

  correctness : ¬ (φ₀ ∧ φ₁) ⟺ ψ₀ ∨ ψ₁
  correctness ϱ rewrite deMorganAnd φ₀ φ₁ ϱ |
                        φ₀⟺ψ₀ ϱ |
                        φ₁⟺ψ₁ ϱ = refl
            
wnnf′ (¬ (φ₀ ⇒ φ₁)) with wnnf′ φ₀ | wnnf′ (¬ φ₁)
... | ψ₀ , WNNFψ₀ , φ₀⟺ψ₀
    | ψ₁ , WNNFψ₁ , φ₁⟺ψ₁ = ψ₀ ∧ ψ₁ , WNNFψ₀ ∧ WNNFψ₁ , correctness where

  correctness : ¬ (φ₀ ⇒ φ₁) ⟺ ψ₀ ∧ ψ₁
  correctness ϱ rewrite deMorganImplies φ₀ φ₁ ϱ |
                        φ₀⟺ψ₀ ϱ |
                        φ₁⟺ψ₁ ϱ = refl
            
wnnf′ (¬ (φ₀ ⇔ φ₁)) with wnnf′ φ₀ | wnnf′ (¬ φ₁)
... | ψ₀ , WNNFψ₀ , φ₀⟺ψ₀
    | ψ₁ , WNNFψ₁ , φ₁⟺ψ₁ = ψ₀ ⇔ ψ₁ , WNNFψ₀ ⇔ WNNFψ₁ , correctness where

  correctness : ¬ (φ₀ ⇔ φ₁) ⟺ ψ₀ ⇔ ψ₁
  correctness ϱ rewrite deMorganIff-right φ₀ φ₁ ϱ |
                        φ₀⟺ψ₀ ϱ |
                        φ₁⟺ψ₁ ϱ = refl
            
wnnf′ (φ₀ ∨ φ₁) with wnnf′ φ₀ | wnnf′ φ₁
... | ψ₀ , WNNFψ₀ , φ₀⟺ψ₀
    | ψ₁ , WNNFψ₁ , φ₁⟺ψ₁ = ψ₀ ∨ ψ₁ , WNNFψ₀ ∨ WNNFψ₁ , correctness where

  correctness : φ₀ ∨ φ₁ ⟺ ψ₀ ∨ ψ₁
  correctness ϱ rewrite φ₀⟺ψ₀ ϱ |
                        φ₁⟺ψ₁ ϱ = refl

wnnf′ (φ₀ ∧ φ₁) with wnnf′ φ₀ | wnnf′ φ₁
... | ψ₀ , WNNFψ₀ , φ₀⟺ψ₀
    | ψ₁ , WNNFψ₁ , φ₁⟺ψ₁ = ψ₀ ∧ ψ₁ , WNNFψ₀ ∧ WNNFψ₁ , correctness where

  correctness : φ₀ ∧ φ₁ ⟺ ψ₀ ∧ ψ₁
  correctness ϱ rewrite φ₀⟺ψ₀ ϱ |
                        φ₁⟺ψ₁ ϱ = refl

wnnf′ (φ₀ ⇒ φ₁) with wnnf′ φ₀ | wnnf′ φ₁
... | ψ₀ , WNNFψ₀ , φ₀⟺ψ₀
    | ψ₁ , WNNFψ₁ , φ₁⟺ψ₁ = ψ₀ ⇒ ψ₁ , WNNFψ₀ ⇒ WNNFψ₁ , correctness where

  correctness : φ₀ ⇒ φ₁ ⟺ ψ₀ ⇒ ψ₁
  correctness ϱ rewrite φ₀⟺ψ₀ ϱ |
                        φ₁⟺ψ₁ ϱ = refl

wnnf′ (φ₀ ⇔ φ₁) with wnnf′ φ₀ | wnnf′ φ₁
... | ψ₀ , WNNFψ₀ , φ₀⟺ψ₀
    | ψ₁ , WNNFψ₁ , φ₁⟺ψ₁ = ψ₀ ⇔ ψ₁ , WNNFψ₀ ⇔ WNNFψ₁ , correctness where

  correctness : φ₀ ⇔ φ₁ ⟺ ψ₀ ⇔ ψ₁
  correctness ϱ rewrite φ₀⟺ψ₀ ϱ |
                        φ₁⟺ψ₁ ϱ = refl
```
~~~~

## Formula size

One of the advantages of the !ref(WNNF) is to simplify the structure of the formula w.r.t. negation without negatively (pun not intended) impacting its size.
As we will see, stronger normal forms such as !ref(NNF), !ref(DNF), and !ref(CNF) unavoidably cause an exponential blowup in the formula size.

There are many ways to assign a size to a formula.
We assign size one to atomic formulas !remoteRef(part1)(Semantics)(Formula)(⊥), !remoteRef(part1)(Semantics)(Formula)(⊤), and !remoteRef(part1)(Semantics)(Formula)(`_), and the size of non-atomic formulas is the sum of the sizes of their immediate subformulas increased by one:

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

In other words, the formula size is the number of nodes of the formula seen as a tree.

!example(#example:size)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The size of the previous formula ``ψ₂ = ¬ ` p₀ ⇒ (` p₁ ⇔ ¬ ` p₂) `` is `7`:

```
_ : size ψ₂ ≡ 7
_ = refl
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

!exercise(#exercise:size-neg)(`size-¬`)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Prove that !ref(size) satisfies the following inequality:

```
size-¬ : ∀ φ → size φ ≤ size (¬ φ)
```

(This will be used below.)

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
```
size-¬ _ = n≤sucn
-- size-¬¬ φ = trans-≤ (size-¬ φ) (size-¬ (¬ φ)) 
```
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We need to find an estimate of the formula size blowup incurred by !ref(wnnf).
First of all, an equality of the form `size (wnnf φ) ≡ e` where `e` is some simple arithmetic function of `size φ`
will not work, since there are formulas of the same size for which the size of their !ref(WNNF) differ,
such as `` ¬ ¬ ` p₀ `` and `` ` p₀ ∧ ` p₁ `` (both of size 3),
whose !ref(WNNF) have size 1 and, resp., 3.

We thus need to guess an inequality `size (wnnf φ) ≤ e`.
We make an "educated guess" and assume that the !ref(WNNF) satisfies an inequality of the form

    size (wnnf φ) ≤ a * size φ + b,

where `a` and `b` are integer parameters whose values have to be found.
We now setup some constraints on `a` and `b` based on the shape of `φ`.
When `φ ≡ ⊥` is an atomic formula, we have `size (wnnf ⊥) ≤ a * size ⊥ + b`,
yielding the constraint (since `wnnf ⊥ ≡ ⊥` and `size ⊥ ≡ 1`)

    1 ≤ a + b.

The same constraint is obtained for the cases `φ ≡ ⊤` and `` φ ≡ ` p ``.
When `φ ≡ ψ ∨ ξ` is a disjunction, for the l.h.s. we have
`size (wnnf (ψ ∨ ξ)) ≡ size (wnnf ψ ∨ wnnf ξ) ≡ 1 + size (wnnf ψ) + size (wnnf ξ)`
which by inductive assumption is `≤ 1 + (a * size ψ + b) + (a * size ξ + b)`,
and for the r.h.s. we have `a * size (ψ ∨ ξ) + b ≡ a * (1 + size ψ + size ξ) + b`.
Putting the two together we must have `1 + (a * size ψ + b) + (a * size ξ + b) ≤ a * (1 + size ψ + size ξ) + b`,
which after some simplification yields

    1 + b ≤ a.

The same constraint is obtained for the other binary connectives.
When `φ ≡ ¬ ¬ ψ`, for the l.h.s. we have
`size (wnnf (¬ ¬ ψ)) ≡ size (wnnf ψ)`
which by inductive assumption is `≤ a * size ψ + b`,
and for the r.h.s. we have `a * size (¬ ¬ ψ) + b ≡ a * (2 + size ψ) + b`.
Putting the two together we must have `a * size ψ + b ≤ a * (2 + size ψ) + b`,
which after some simplification yields

    0 ≤ a * 2.

When `φ ≡ ¬ (ψ ∨ ξ)`, for the l.h.s. we have
`size (wnnf (¬ (ψ ∨ ξ))) ≡ size (wnnf (¬ ψ) ∧ wnnf (¬ ξ)) ≡ 1 + size (wnnf (¬ ψ)) + size (wnnf (¬ ξ))`
which by inductive assumption is `≤ 1 + (a * (1 + size ψ) + b) + (a * (1 + size ξ) + b)`,
and for the r.h.s. we have `a * size (¬ (ψ ∨ ξ)) + b ≡ a * (2 + size ψ + size ξ) + b`.
Putting the two together we must have `1 + (a * (1 + size ψ) + b) + (a * (1 + size ξ) + b) ≤ a * (2 + size ψ + size ξ) + b`,
which after some simplification yields

    1 + b ≤ 0.

The same constraint is obtained in the dual case `φ ≡ ¬ (ψ ∧ ξ)`.
When `φ ≡ ¬ (ψ ⇒ ξ)`, for the l.h.s. we have
`size (wnnf (¬ (ψ ⇒ ξ))) ≡ size (wnnf ψ ∧ wnnf (¬ ξ)) ≡ 1 + size (wnnf ψ) + size (wnnf (¬ ξ))`
which by inductive assumption is `≤ 1 + (a * size ψ + b) + (a * (1 + size ξ) + b)`,
and for the r.h.s. we have `a * size (¬ (ψ ⇒ ξ)) + b ≡ a * (2 + size ψ + size ξ) + b`.
Putting the two together we must have `1 + (a * size ψ + b) + (a * (1 + size ξ) + b) ≤ a * (2 + size ψ + size ξ) + b`,
which after some simplification yields

    1 + b ≤ a.

The same constraint is obtained in the case `φ ≡ ¬ (ψ ⇔ ξ)`.
The optimal solution for all the constraints above is `a ≡ 2` and `b ≡ - 1`.
An analogous analysis for negated formulas can be carried out.
Altogether, this yields the following inductive statements:

```
wnnf-size : ∀ φ → size (wnnf φ) ≤ 2 * size φ ∸ 1
wnnf-size-¬ : ∀ φ → size (wnnf (¬ φ)) ≤ 2 * size φ
```

!hide
~~~~
For negated formulas, !ref(wnnf-size-¬) provides an upper bound stronger than !ref(wnnf-size).
The proof proceeds by structural induction using some elementary arithmetical facts.
~~~~
~~~~
```
postulate
  size-reasoning : ∀ {a b} c d →
    a ≤ 2 * c ∸ 1 →
    b ≤ 2 * d ∸ 1 →
    -------------------------------
    1 + a + b ≤ 2 * (1 + c + d) ∸ 1

  size-reasoning-¬1 : ∀ {a b} c d →
    a ≤ 2 * c →
    b ≤ 2 * d →
    ---------------------------
    1 + a + b ≤ 2 * (1 + c + d)

  size-reasoning-¬2 : ∀ {a b} c d →
    a ≤ 2 * c ∸ 1 →
    b ≤ 2 * d →
    ---------------------------
    1 + a + b ≤ 2 * (1 + c + d)
```

The base cases for !ref(wnnf-size) are immediate:

```
wnnf-size ⊥ = s≤s 0≤n
wnnf-size ⊤ = s≤s 0≤n
wnnf-size (` p) = s≤s 0≤n
```

In the case of negation,
we rely on !ref(wnnf-size-¬):

```
wnnf-size (¬ φ)
  with wnnf-size-¬ φ
... | ind¬φ = begin≤
  size (wnnf (¬ φ)) ≤⟨ ind¬φ ⟩
  2 * size φ ≤⟨ n≤sucn ⟩
  suc (2 * size φ) ≤≡⟨ sucm+n≡m+sucn {size φ} {size φ} ⟩
  size φ + suc (size φ) ∎≤
```

For disjunctions, we provide a complete analysis:

```
wnnf-size (φ ∨ ψ)
  with wnnf-size φ | wnnf-size ψ
... | indφ | indψ = begin≤
   size (wnnf (φ ∨ ψ)) ≤⟨⟩
   size (wnnf φ ∨ wnnf ψ) ≤⟨⟩
   1 + size (wnnf φ) + size (wnnf ψ) ≤⟨ size-reasoning (size φ) (size ψ) indφ indψ ⟩
   2 * size (φ ∨ ψ) ∸ 1 ∎≤
```

The last three cases are similar and we give them in a shortened form:

```
wnnf-size (φ ∧ ψ) = size-reasoning (size φ) (size ψ) (wnnf-size φ) (wnnf-size ψ)
wnnf-size (φ ⇒ ψ) = size-reasoning (size φ) (size ψ) (wnnf-size φ) (wnnf-size ψ)
wnnf-size (φ ⇔ ψ) = size-reasoning (size φ) (size ψ) (wnnf-size φ) (wnnf-size ψ)
```

The base cases for !ref(wnnf-size-¬) are immediate:

```
wnnf-size-¬ ⊥ = s≤s 0≤n
wnnf-size-¬ ⊤ = s≤s 0≤n
wnnf-size-¬ (` p) = s≤s (s≤s 0≤n)
```

In the case of negation,
since a double negation is eliminated, we rely on !ref(wnnf-size):

```
wnnf-size-¬ (¬ φ)
  with wnnf-size φ
... | indφ = begin≤
  size (wnnf φ) ≤⟨ indφ ⟩
  2 * size φ ∸ 1 ≤⟨ m∸n≤m (2 * size φ) 1 ⟩
  2 * size φ ≤⟨ cong-≤ (Num 2 *C □) (size-¬ φ) ⟩
  2 * size (¬ φ) ∎≤
```

The cases of binary connectives are also simple:

```
wnnf-size-¬ (φ ∨ ψ) = size-reasoning-¬1 (size φ) (size ψ) (wnnf-size-¬ φ) (wnnf-size-¬ ψ)
wnnf-size-¬ (φ ∧ ψ) = size-reasoning-¬1 (size φ) (size ψ) (wnnf-size-¬ φ) (wnnf-size-¬ ψ)
wnnf-size-¬ (φ ⇒ ψ) = size-reasoning-¬2 (size φ) (size ψ) (wnnf-size φ) (wnnf-size-¬ ψ)
wnnf-size-¬ (φ ⇔ ψ) = size-reasoning-¬2 (size φ) (size ψ) (wnnf-size φ) (wnnf-size-¬ ψ)
```
~~~~

!exercise(#exercise:wnnf-tight)
~~~~
On which kind of formulas does the !ref(WNNF) translation performed by !ref(wnnf) achieve maximal blow-up?
Is the bound provided by !ref(wnnf-size-¬) tight?
~~~~
~~~~
The worst case of the !ref(WNNF) translation is achieved when a single negation is pushed inside a formula of size `2*n` the form `` ¬ (` p₁ ∨ ⋯ ∨ ` pₙ) ``,
yielding a !ref(WNNF) formula `` ¬ ` p₁ ∨ ⋯ ∨ ¬ ` pₙ `` of size `3*n-1`.
The bound given by !ref(wnnf-size-¬) in this case would be `4*n`,
which thus is not tight in general.
~~~~

# Negation normal form {#NNF}

A propositional formula `φ` is in *negation normal form* (NNF) if it uses only the connectives
!remoteRef(part1)(Semantics)(Formula)(⊥),
!remoteRef(part1)(Semantics)(Formula)(⊤),
!remoteRef(part1)(Semantics)(Formula)(¬_),
!remoteRef(part1)(Semantics)(Formula)(_∨_), and
!remoteRef(part1)(Semantics)(Formula)(_∧_),
and negation appears only in front of propositional variables, i.e., inside literals.
In other words, a NNF formula is a !ref(WNNF) without the implication !remoteRef(part1)(Semantics)(Formula)(_⇒_) and bi-implication !remoteRef(part1)(Semantics)(Formula)(_⇔_) connectives.
This is captured by the following definition[^NNF-departure]:

[^NNF-departure]: We slightly depart from a more standard definition of NNF,
whereby !remoteRef(part1)(Semantics)(Formula)(⊥) and !remoteRef(part1)(Semantics)(Formula)(⊤) are not allowed as proper subformulas of an NNF formula.
In other words, according to our definition `` ` p₀ ∨ ⊥ `` is in NNF, while it is not according to the more restrictive one.
By applying !remoteRef(part1)(Semantics)(simplify) as a preprocessing step we can remove such occurrences of !remoteRef(part1)(Semantics)(Formula)(⊥), !remoteRef(part1)(Semantics)(Formula)(⊤).
Formally proving that the resulting formulas do not contain !remoteRef(part1)(Semantics)(Formula)(⊥), !remoteRef(part1)(Semantics)(Formula)(⊤) as proper subformulas, while possible, would introduce an extra overhead obscuring the main point about NNF,
which is the handling of negation.
For this reason, we stick here to our slightly more relaxed NNF definition.

```
data NNF : Formula → Set where
  ⊤ : NNF ⊤
  ⊥ : NNF ⊥
  `_ : (p : PropName) → NNF (` p)
  ¬`_ : (p : PropName) → NNF (¬ ` p)
  _∧_ : NNF φ → NNF ψ → NNF (φ ∧ ψ)
  _∨_ : NNF φ → NNF ψ → NNF (φ ∨ ψ)
```

Given a formula `φ`, we can decide whether it is in !ref(NNF) or not:

```
NNF? : ∀ φ → Dec (NNF φ)
```

!hide
~~~
The proof works by inspecting `φ` sufficiently deeply.
~~~
~~~
```
NNF? ⊥ = yes ⊥
NNF? ⊤ = yes ⊤
NNF? (` p) = yes (` p)

NNF? (¬ ⊥) = no λ ()
NNF? (¬ ⊤) = no λ ()
NNF? (¬ (` p)) = yes (¬` p)
NNF? (¬ (¬ _)) = no λ ()
NNF? (¬ (_ ∨ _)) = no λ ()
NNF? (¬ (_ ∧ _)) = no λ ()
NNF? (¬ (_ ⇒ _)) = no λ ()
NNF? (¬ (_ ⇔ _)) = no λ ()

NNF? (φ ∨ ψ)
  with NNF? φ |
       NNF? ψ
... | yes nnfφ | yes nnfψ = yes (nnfφ ∨ nnfψ)
... | no ¬nnfφ | _ = no λ{ (nnfφ ∨ _) → ¬nnfφ nnfφ}
... | _ | no ¬nnfψ = no λ{ (_ ∨ nnfψ) → ¬nnfψ nnfψ}

NNF? (φ ∧ ψ)
  with NNF? φ |
       NNF? ψ
... | yes nnfφ | yes nnfψ = yes (nnfφ ∧ nnfψ)
... | no ¬nnfφ | _ = no λ{ (nnfφ ∧ _) → ¬nnfφ nnfφ}
... | _ | no ¬nnfψ = no λ{ (_ ∧ nnfψ) → ¬nnfψ nnfψ}

NNF? (_ ⇒ _) = no λ ()
NNF? (_ ⇔ _) = no λ ()
```
~~~

```
ξ₀ ξ₁ ξ₂ ξ₃ ξ₄ ξ₅ : Formula
```

::::::::::::: {.inlinecode}

For instance, the formulas
```
ξ₀ = ⊤
```
and
```
ξ₁ = ¬ ` p₀ ∨ ` p₁
```
are in !ref(NNF), while the following formulas are not:
```
ξ₂ = ¬ ⊤
```
(negation not in front of a propositional variable) and
```
ξ₃ = ` p₀ ⇒ ` p₁
```
(it contains an implication connective), as we automatically check:

:::::::::::::

```
_ : All? NNF? ([ ξ₀ ξ₁ ]) ×? All? (~?_ ∘ NNF?) ([ ξ₂ ξ₃ ]) ≡ yes _
_ = refl
```

!hide
~~~
The only difference between !ref(WNNF) and !ref(NNF) is that in the latter we addionally forbid implications and bi-implications.
Moreover, if a formula does not contain implications/bi-implications in the first place,
then !ref(wnnf) does not introduce them and thus it produces an !ref(NNF) formula:

```
wnnf-impFree : Formula[⊥,⊤,¬,∨,∧] φ → NNF (wnnf φ)
```

The proof proceeds by induction on the evidence that the formula is in the `Formula[⊥,⊤,¬,∨,∧]` form.
~~~
~~~
```
wnnf-impFree ⊥ = ⊥
wnnf-impFree ⊤ = ⊤
wnnf-impFree (` p) = ` p
wnnf-impFree (¬ ⊥) = ⊤
wnnf-impFree (¬ ⊤) = ⊥
wnnf-impFree (¬ ` p) = ¬` p
wnnf-impFree (¬ ¬ view-φ) = wnnf-impFree view-φ
wnnf-impFree (¬ (view-φ ∨ view-ψ)) = wnnf-impFree (¬ view-φ) ∧ wnnf-impFree (¬ view-ψ)
wnnf-impFree (¬ (view-φ ∧ view-ψ)) = wnnf-impFree (¬ view-φ) ∨ wnnf-impFree (¬ view-ψ)
wnnf-impFree (view-φ ∨ view-ψ) = wnnf-impFree view-φ ∨ wnnf-impFree view-ψ
wnnf-impFree (view-φ ∧ view-ψ) = wnnf-impFree view-φ ∧ wnnf-impFree view-ψ
```
~~~

In order to transform a formula to !ref(NNF) we can

1) Remove implications and bi-implications, and
2) Transform the formula to !ref(WNNF).

The second step is achieved by !ref(wnnf).
In the next section we focus on the first step.

## Remove implications and bi-implications

The function !ref(removeImp) below removes implications and bi-implications by expanding them according to the tautologies
(c.f. !remoteRef(part1)(Semantics)(expandImplies), resp., !remoteRef(part1)(Semantics)(expandIff)):

    φ ⇒ ψ ⟺ ¬ φ ∨ ψ
    φ ⇔ ψ ⟺ (¬ φ ∨ ψ) ∧ (φ ∨ ¬ ψ)

!hide
~~~~
```
removeImp : Formula → Formula
removeImp-sound : ∀ φ → φ ⟺ removeImp φ
```
Both !ref(removeImp) and its soundness proof !ref(removeImp-sound) are defined by a customary structural induction.
~~~~
~~~~
```
removeImp ⊥ = ⊥
removeImp ⊤ = ⊤
removeImp (` p) = ` p
removeImp (¬ φ) = ¬ removeImp φ
removeImp (φ ∨ ψ) = removeImp φ ∨ removeImp ψ
removeImp (φ ∧ ψ) = removeImp φ ∧ removeImp ψ
removeImp (φ ⇒ ψ) = ¬ removeImp φ ∨ removeImp ψ
removeImp (φ ⇔ ψ)
  with φ́ ← removeImp φ | ψ́ ← removeImp ψ
  = (¬ φ́ ∨ ψ́) ∧ (φ́ ∨ ¬ ψ́)
```

```
removeImp-sound ⊥ ϱ = refl
removeImp-sound ⊤ ϱ = refl
removeImp-sound (` p) ϱ = refl
removeImp-sound (¬ φ) ϱ
  rewrite removeImp-sound φ ϱ = refl
removeImp-sound (φ ∨ ψ) ϱ
  rewrite removeImp-sound φ ϱ |
          removeImp-sound ψ ϱ = refl
removeImp-sound (φ ∧ ψ) ϱ
  rewrite removeImp-sound φ ϱ |
          removeImp-sound ψ ϱ = refl
removeImp-sound (φ ⇒ ψ) ϱ
  rewrite removeImp-sound φ ϱ |
          removeImp-sound ψ ϱ |
          expandImplies (removeImp φ) (removeImp ψ) ϱ = refl
removeImp-sound (φ ⇔ ψ) ϱ
  rewrite removeImp-sound φ ϱ |
          removeImp-sound ψ ϱ |
          expandIff (removeImp φ) (removeImp ψ) ϱ = refl
```
~~~~

!hide
~~~~
Unsurprisingly but importantly, `removeImp φ` does not contain either implications or bi-implications
```
removeImp-impFree : ∀ φ → Formula[⊥,⊤,¬,∨,∧] (removeImp φ)
```
~~~~
~~~~
```
removeImp-impFree ⊥ = ⊥
removeImp-impFree ⊤ = ⊤
removeImp-impFree (` p) = ` p
removeImp-impFree (¬ φ) = ¬ removeImp-impFree φ
removeImp-impFree (φ ∨ ψ) = removeImp-impFree φ ∨ removeImp-impFree ψ
removeImp-impFree (φ ∧ ψ) = removeImp-impFree φ ∧ removeImp-impFree ψ
removeImp-impFree (φ ⇒ ψ) = ¬ removeImp-impFree φ ∨ removeImp-impFree ψ
removeImp-impFree (φ ⇔ ψ) = (¬ removeImp-impFree φ ∨ removeImp-impFree ψ) ∧
                              (removeImp-impFree φ ∨ ¬ removeImp-impFree ψ)
```
~~~~

## Transformation to !ref(NNF)

We are now ready to put the pieces together.
The transformation to !ref(NNF) proceeds by simplifying the formula (this removes the zero-ary connectives `⊤` and `⊥`, even though we won't formally prove this is the case), by removing implications/bi-implications, and by transforming to !ref(WNNF):

```
nnf : Formula → Formula
nnf = wnnf ∘ removeImp ∘ simplify
```

::::::::::::: {.inlinecode}

For example, the formula
```
ξ₄ = ¬ ¬ (` p₀ ⇒ ¬ (` p₁ ∧ ` p₂ ∧ ⊤))
```
is transformed to the !ref(NNF) formula
```
ξ₅ = ¬ ` p₀ ∨ ¬ ` p₁ ∨ ¬ ` p₂
```
as proved below:

:::::::::::::

```
_ : nnf ξ₄ ≡ ξ₅ × NNF? ξ₅ ≡ yes _
_ = refl , refl
```

!exercise(#exercise:nnf-complexity)
~~~~
What is the size blowup of !ref(nnf)? On which kind of formulas is it achieved?
~~~~
~~~~
The !ref(nnf) transformation is exponential on formulas of the form `φ₀ ⇔ φ₁ ⇔ ⋯ ⇔ φₙ`,
the culprit being !ref(removeImp):
every time a bi-implication is removed the formula size doubles.
Avoiding such blow-up is the main advantage of !ref(WNNF) over !ref(NNF), if the weaker form suffices.
On the other hand, if there are no bi-implications, !ref(nnf) has linear complexity, pretty much like !ref(wnnf).
~~~~


## Correctness

The correctness of the !ref(NNF) translation follows from the previous considerations:

```
nnf-NNF : ∀ φ → NNF (nnf φ)
nnf-NNF φ = wnnf-impFree (removeImp-impFree (simplify φ))
```

```
nnf-sound : ∀ φ → φ ⟺ nnf φ
nnf-sound φ ϱ
  rewrite sym (wnnf-sound (removeImp (simplify φ)) ϱ) |
          sym (removeImp-sound (simplify φ) ϱ) |
          sym (simplify-sound φ ϱ) = refl
```

The !ref(NNF) is the most basic normal form of interest.
In the following sections we will study stronger normal forms.

# Disjunctive normal form {#DNF}

A *clause* `C` is a conjunction of literals `l1 ∧ ⋯ ∧ lm`.
A formula is in *disjunctive normal form* (DNF) if it is a disjunction of clauses `C1 ∨ ⋯ ∨ Cn`.
When discussing formulas in DNF it is customary to use a list-like notation[^DNF-middle-constructors]:

```
data Literal : Formula → Set where
  Pos : (p : PropName) → Literal (` p)
  Neg : (p : PropName) → Literal (¬ (` p))
  
data DNFClause : Formula → Set where
  ∅ : DNFClause ⊤
  _∙ : Literal φ → DNFClause φ
  _,_ : Literal φ → DNFClause ψ → DNFClause (φ ∧ ψ)

data DNF : Formula  → Set where
  ∅ : DNF ⊥
  _∙ : DNFClause φ → DNF φ
  _,_ : DNFClause φ → DNF ψ → DNF (φ ∨ ψ)

infix 11 _∙
```

[^DNF-middle-constructors]: The middle constructors of the form `_∙` allow us to avoid always appending a `⊥` or `⊤` to !ref(DNFClause), resp., !ref(DNF) formulas.
This introduces a slight overhead in the following code,
but allows formulas such as `` ` p₀ `` to be already in !ref(DNF),
instead of considering the more cumbersome `` ` p₀ ∧ ⊤ ∨ ⊥ ``.

!hide
~~~
We conventionally allow `⊤` to be a !ref(DNFClause) and similarly `⊥` to be a !ref(DNF), in line with !ref(NNF).
All the notions of !ref(Literal), !ref(DNFClause), and !ref(DNF) are decidable (proved by a standard inductive argument):

```
Literal? : ∀ φ → Dec (Literal φ)
DNFClause? : ∀ φ → Dec (DNFClause φ)
DNF? : ∀ φ → Dec (DNF φ)
```
~~~
~~~
```
Literal? ⊥ = no λ ()
Literal? ⊤ = no λ ()
Literal? (` p) = yes (Pos p)
Literal? (¬ ⊥) = no λ ()
Literal? (¬ ⊤) = no λ ()
Literal? (¬ (` p)) = yes (Neg p)
Literal? (¬ (¬ φ)) = no λ ()
Literal? (¬ (φ ∨ ψ)) = no λ ()
Literal? (¬ (φ ∧ ψ)) = no λ ()
Literal? (¬ (φ ⇒ ψ)) = no λ ()
Literal? (¬ (φ ⇔ ψ)) = no λ ()
Literal? (φ ∨ ψ) = no λ ()
Literal? (φ ∧ ψ) = no λ ()
Literal? (φ ⇒ ψ) = no λ ()
Literal? (φ ⇔ ψ) = no λ ()
```

```
DNFClause? ⊥ = no λ{(() ∙)}
DNFClause? ⊤ = yes ∅
DNFClause? (` p) = yes (Pos p ∙)

DNFClause? (¬ ⊥) = no λ{(() ∙)}
DNFClause? (¬ ⊤) = no λ{(() ∙)}
DNFClause? (¬ (` p)) = yes (Neg p ∙)
DNFClause? (¬ (¬ φ)) = no λ{(() ∙)}
DNFClause? (¬ (φ ∨ ψ)) = no λ{(() ∙)}
DNFClause? (¬ (φ ∧ ψ)) = no λ{(() ∙)}
DNFClause? (¬ (φ ⇒ ψ)) = no λ{(() ∙)}
DNFClause? (¬ (φ ⇔ ψ)) = no λ{(() ∙)}

DNFClause? (φ ∨ ψ) = no λ{(() ∙)}

DNFClause? (φ ∧ ψ)
  with Literal? φ | DNFClause? ψ
... | yes Literalφ | yes DNFClauseψ = yes (Literalφ , DNFClauseψ)
... | yes _ | no ~DNFClauseψ = no λ{(_ , DNFClauseψ) → ~DNFClauseψ DNFClauseψ}
... | no ~Literalφ | _ = no λ{(Literalφ , _) → ~Literalφ Literalφ}

DNFClause? (φ ⇒ ψ) = no λ{(() ∙)}
DNFClause? (φ ⇔ ψ) = no λ{(() ∙)}
```

```
DNF? ⊥ = yes ∅
DNF? ⊤ = yes (∅ ∙)
DNF? (` p) = yes (Pos p ∙ ∙)
DNF? (¬ ⊥) = no λ{(() ∙ ∙)}
DNF? (¬ ⊤) = no λ{(() ∙ ∙)}
DNF? (¬ (` p)) = yes (Neg p ∙ ∙)
DNF? (¬ (¬ φ)) = no λ{(() ∙ ∙)}
DNF? (¬ (φ ∨ ψ)) = no λ{(() ∙ ∙)}
DNF? (¬ (φ ∧ ψ)) = no λ{(() ∙ ∙)}
DNF? (¬ (φ ⇒ ψ)) = no λ{(() ∙ ∙)}
DNF? (¬ (φ ⇔ ψ)) = no λ{(() ∙ ∙)}

DNF? (φ ∨ ψ)
  with DNFClause? φ | DNF? ψ
... | yes DNFClauseφ | yes DNFψ = yes (DNFClauseφ , DNFψ)
... | yes _ | no ~DNFψ = no λ{ (() ∙ ∙); (_ , DNFψ) → ~DNFψ DNFψ}
... | no ~DNFClauseφ | _ = no λ{ (() ∙ ∙); (DNFClauseφ , _) → ~DNFClauseφ DNFClauseφ}
  
DNF? (φ ∧ ψ) with DNFClause? (φ ∧ ψ)
... | yes DNFClause = yes (DNFClause ∙)
... | no ~DNFClause = no λ{ (DNFClause ∙) → ~DNFClause DNFClause}

DNF? (φ ⇒ ψ) = no λ{(() ∙ ∙)}
DNF? (φ ⇔ ψ) = no λ{(() ∙ ∙)}

ζ₀ ζ₁ ζ₂ : Formula 
```
~~~

::::::::::::: {.inlinecode}

Thus a !ref(DNF) formula is an !ref(NNF) formula where we further constrain the way !remoteRef(part0)(Semantics)(Formula)(_∨_) and !remoteRef(part0)(Semantics)(Formula)(_∧_) nest: While in !ref(NNF) there is no restriction on nesting,
in !ref(DNF) we demand that the formula is a "disjunction of conjunctions".
For example,
```
ζ₀ = (` p₀ ∧ ¬ ` p₁) ∨ ` p₂
```
is in !ref(DNF),
but the following formulas are not:
```
ζ₁ = ¬ ¬ ` p₂
```
(double negation, not even in !ref(NNF)),
```
ζ₂ = ` p₀ ∧ (` p₁ ∨ ` p₂)
```
(disjunction inside a conjunction).

:::::::::::::

```
_ : DNF? ζ₀ ×? All? (~?_ ∘ DNF?) ([ ζ₁ ζ₂ ]) ≡ yes _
_ = refl
```

In the rest of the section we show how to convert an arbitrary formula to an equivalent one in !ref(DNF).
In fact, we have already seen a method achieving this:
When discussing functional completeness for the fragment containing only
!flexRef(part1)(CharacteristicFormulas)(sec:fragmentOrAndNeg)(conjunction, disjunction, and negation) we have shown such a method based on characteristic formulas.
This was performed by !remoteRef(part1)(CharacteristicFormulas)(funCompl[¬∨∧]) and as a matter of fact it produces a formula in !ref(DNF),
even though we have not proved this.
The drawback is that the method based on characteristic formulas essentially relies on enumerating all satisfying valuations
and thus 1) it always takes exponential time to produce the output formula,
and 2) it produces !ref(DNF) formulas which are as big as the number of their satisfying valuations.
For instance, in the extreme case of a tautology such as `⊤` (which is already in !ref(DNF)!),
this will produce a formula of exponential size.

While in general an exponential blow-up is unavoidable when translating a formula to !ref(DNF),
we will explore here a syntactical approach which avoids the blow-up at least in some "easy" cases.

!exercise(#exercise:merge-DNF-clauses)
~~~
As a warm up, show that we can "conjunctively merge" two clauses,
and similarly "disjunctively merge" two DNF's (as in list concatenation),
while preserving the semantics:

```
_+∧+_ : DNFClause φ →
          DNFClause ψ →
          -------------------------------
          ∃[ ξ ] DNFClause ξ × φ ∧ ψ ⟺ ξ
          
_+++∨+++_ : DNF φ →
          DNF ψ →
          -------------------------
          ∃[ ξ ] DNF ξ × φ ∨ ψ ⟺ ξ
```
~~~
~~~
```
_+∧+_ {⊤} {ψ} ∅ Cψ = ψ , Cψ , correctness where

  correctness : ⊤ ∧ ψ ⟺ ψ
  correctness ϱ with ⟦ ψ ⟧ ϱ
  ... | tt = refl
  ... | ff = refl

_+∧+_ {φ} {ψ} (Lφ ∙) Cψ = φ ∧ ψ , (Lφ , Cψ) , λ ϱ → refl
  
_+∧+_ {φ ∧ φ'} {ψ} (Lφ , Cφ') Cψ
  with Cφ' +∧+ Cψ
... | ξ , Cξ , φ'∧ψ⟺ξ = φ ∧ ξ , (Lφ , Cξ) , correctness where

  correctness : (φ ∧ φ') ∧ ψ ⟺ φ ∧ ξ
  correctness ϱ rewrite sym (φ'∧ψ⟺ξ ϱ) = assocAnd φ φ' ψ ϱ
```

```
_+++∨+++_ {⊥} {ψ} ∅ DNFψ = ψ , DNFψ , correctness where

  correctness : ⊥ ∨ ψ ⟺ ψ
  correctness ϱ with ⟦ ψ ⟧ ϱ
  ... | tt = refl
  ... | ff = refl

_+++∨+++_ {φ} {ψ} (Cφ ∙) DNFψ = φ ∨ ψ , (Cφ , DNFψ) , λ ϱ → refl

_+++∨+++_ {φ ∨ ψ} {ξ} (Cφ , DNFψ) DNFξ
  with DNFψ +++∨+++ DNFξ
... | η , DNFη , ψ∨ξ⟺η = φ ∨ η , (Cφ , DNFη) , correctness where

  correctness : (φ ∨ ψ) ∨ ξ ⟺ φ ∨ η
  correctness ϱ rewrite assocOr φ ψ ξ ϱ | ψ∨ξ⟺η ϱ = refl
```
~~~

We build !ref(DNF) formulas using the distributivity of conjunction over disjunction.
In the case of a formula distributing over the disjunction of two formulas,
we have the *left distributivity rule* (c.f. !remoteRef(part1)(Semantics)(distrAndOr-left)):

    φ ∧ (ψ ∨ ξ) ⟺ φ ∧ ψ ∨ φ ∧ ξ.

When `φ` and `ψ` are two clauses and `ξ` is a DNF,
this gives us a recipe to inductively construct a DNF
whose first clause is `φ ∧ ψ` (obtained by joining together two clauses with !ref(_+∧+_) and the rest of the DNF is recursively obtained by examining `φ ∧ ξ`:

```
infixr 9 _++∧++_
_++∧++_ : DNFClause φ → DNF ψ → ∃[ ξ ] DNF ξ × φ ∧ ψ ⟺ ξ
_++∧++_ {φ} {⊥} Cφ ∅ = ⊥ , ∅ , λ ϱ → refl

_++∧++_ {φ} {ψ} Cφ (Cψ ∙)
  with Cφ +∧+ Cψ
... | φψ , Cφψ , φ∧ψ⟺φψ = φψ , Cφψ ∙ , φ∧ψ⟺φψ

_++∧++_ {φ} {ψ ∨ ξ} Cφ (Cψ , DNFξ)
  with Cφ +∧+ Cψ |
       Cφ ++∧++ DNFξ
... | φψ , Cφψ , φ∧ψ⟺φψ
    | η , DNFη , φ∧ξ⟺η = φψ ∨ η , (Cφψ , DNFη) , correctness where

  correctness : φ ∧ (ψ ∨ ξ) ⟺ φψ ∨ η
  correctness ϱ rewrite distrAndOr-left φ ψ ξ ϱ |
                        φ∧ψ⟺φψ ϱ |
                        φ∧ξ⟺η ϱ = refl
```

For instance,

```
_ : dfst (Pos p₀ , Neg p₁ ∙ ++∧++ (Pos p₁ , Pos p₂ ∙) , (Neg p₀ , Neg p₂ ∙) ∙) ≡
    ` p₀ ∧ ¬ ` p₁ ∧ ` p₁ ∧ ` p₂ ∨ ` p₀ ∧ ¬ ` p₁ ∧ ¬ ` p₀ ∧ ¬ ` p₂
_ = refl
```

We want to "upgrade" the previous procedure in order to construct the !ref(DNF) for the conjunction of two DNFs.
This is achieved by the following *right distributivity rule* (c.f. !remoteRef(part1)(Semantics)(distrAndOr-right)):

    (φ ∨ ψ) ∧ ξ ⟺ φ ∧ ξc ∨ ψ ∧ ξ,

 where `φ` is a clause and `ψ`, `ξ` are DNFs.
 The rule above gives us a recipe to transform the conjunction of the two DNFs `φ ∨ ψ` and `ξ`
 into a DNF whose first disjunct is `φ ∨ ψ` (computed according to !ref(_++∧++_)) and the rest of which is recursively computed by examining `ψ ∧ ξ`:

```
_+++∧+++_ : DNF φ → DNF ψ → ∃[ ξ ] DNF ξ × φ ∧ ψ ⟺ ξ
_+++∧+++_ {⊥} {ψ} ∅ DNFψ = ⊥ , ∅ , λ ϱ → refl

_+++∧+++_ {φ} {ψ} (Cφ ∙) DNFψ = Cφ ++∧++ DNFψ

_+++∧+++_ {φ ∨ φ'} {ψ} (Cφ , DNFφ') DNFψ
  with Cφ ++∧++ DNFψ    | DNFφ' +++∧+++ DNFψ
... | ξ , DNFξ , φ∧ψ⟺ξ | η , DNFη , φ'∧ψ⟺η
  with DNFξ +++∨+++ DNFη
... | μ , DNFμ , ξ∨η⟺μ = μ , DNFμ , correctness where

  correctness : (φ ∨ φ') ∧ ψ ⟺ μ
  correctness ϱ rewrite
    distrAndOr-right φ φ' ψ ϱ |
    φ'∧ψ⟺η ϱ |
    φ∧ψ⟺ξ ϱ |
    ξ∨η⟺μ ϱ = refl
```

## Basic transformation

We are now ready to present a translation from !ref(NNF) formulas to equivalent !ref(DNF) ones.

```
dnf1 : NNF φ → ∃[ ψ ] DNF ψ × φ ⟺ ψ
```

The base cases are immediate:

```
dnf1 ⊤ = ⊤ , ∅ ∙ , λ ϱ → refl
dnf1 ⊥ = ⊥ , ∅ , λ ϱ → refl
dnf1 (` p) = ` p , Pos p ∙ ∙ , λ ϱ → refl
dnf1 (¬` p) = ¬ ` p , Neg p ∙ ∙ , λ ϱ → refl
```

In the inductive cases (disjunction or conjunction)
we first recursively compute the DNFs of the subformulas and then we combine them.
Disjunctions are easy since DNF formulas are closed under disjunction, with no blowup (c.f. !ref(_+++∨+++_)):

```
dnf1 {φ ∨ ψ} (NNFφ ∨ NNFψ)
  with dnf1 NNFφ          | dnf1 NNFψ
... | φ' , DNFφ' , φ⟺φ' | ψ' , DNFψ' , ψ⟺ψ'
  with DNFφ' +++∨+++ DNFψ'
... | ξ , DNFξ , φ'∨ψ'⟺ξ = ξ , DNFξ , correctness where

  correctness : φ ∨ ψ ⟺ ξ
  correctness ϱ rewrite φ⟺φ' ϱ | ψ⟺ψ' ϱ | φ'∨ψ'⟺ξ ϱ = refl
```

Conjunctions are harder, but !ref(_+++∧+++_) will do the trick:

```
dnf1 {φ ∧ ψ} (NNFφ ∧ NNFψ)
  with dnf1 NNFφ | dnf1 NNFψ
... | φ' , DNFφ' , φ⟺φ' | ψ' , DNFψ' , ψ⟺ψ'
  with DNFφ' +++∧+++ DNFψ'
... | ξ , DNFξ , φ'∧ψ'⟺ξ = ξ , DNFξ , correctness where

  correctness : φ ∧ ψ ⟺ ξ
  correctness ϱ rewrite φ⟺φ' ϱ | ψ⟺ψ' ϱ | φ'∧ψ'⟺ξ ϱ = refl
```

For example,

```
_ : dfst (dnf1 (⊥ ∧ ` p₀)) ≡ ⊥                  ×
    dfst (dnf1 (⊤ ∨ ` p₀)) ≡ ⊤ ∨ ` p₀           ×
    dfst (dnf1 (⊤ ∧ ` p₀ ∧ ` p₀)) ≡ ` p₀ ∧ ` p₀ ×
    dfst (dnf1 (` p₀ ∧ (` p₁ ∨ ¬` p₀))) ≡ ` p₀ ∧ ` p₁ ∨ ` p₀ ∧ ¬ ` p₀

_ = refl , refl , refl , refl
```

We can see that !ref(dnf1) performs some rudimentary form of simplification, e.g., by removing `⊥` in ``⊥ ∧ ` p₀``,
but not all the simplifications we may desire.
For instance ``⊤ ∨ ` p₀`` should be transformed into `⊤` (which could be achieved by !remoteRef(part1)(Semantics)(simplify)).
and 
More significantly, ``⊤ ∧ ` p₀ ∧ ` p₀`` should be transformed to `` ` p₀`` (by removing one duplicate occurrence of `p₀`),
and `` ` p₀ ∧ ` p₁ ∨ ` p₀ ∧ ¬ ` p₀ `` to `` ` p₀ ∧ ` p₁ `` (by removing the unsatisfiable clause `` ` p₀ ∧ ¬ ` p₀ ``).
The latter kind of simplifications is specific to the DNF form, and it will be handled in the next section.

## Simplification

The !ref(DNF) structure allows us to simplify formulas to a stronger extend that what is possible with the generic procedure !remoteRef(part1)(Semantics)(simplify). In this section we explore a simplification procedure which exploits the DNF structure.

We will implement two kind of simplifications,
both based on the fact that a propositional variable should appear at most once in a clause:

1) If a literal appears multiple times in a clause, then its repeated occurrences can be removed.
2) If a literal appears positively and negatively in a clause, then the clause is unsatisfiable and can be removed.

### Case 1: Repeated literals

We define a predicate !ref(_IsInClause_) capturing whether a literal occurs in a clause:

```
infix 10 _IsInClause_
data _IsInClause_ : Literal φ → DNFClause ψ → Set where
  stop1 : ∀ {lit : Literal φ} → lit IsInClause (lit ∙)
  stop2 : ∀ {lit : Literal φ} {C : DNFClause ψ} → lit IsInClause (lit , C)
  skip : ∀ {lit : Literal φ} {lit' : Literal ψ} {C : DNFClause ξ} →
         lit IsInClause C → lit IsInClause (lit' , C)
```

(This is analogous to the list membership predicate !remoteRef(part0)(List)(_∈_),
except that the type of !ref(DNFClause) is more complex than a plain list,
and moreover we have two base cases `stop1` and `stop2`, instead of just one.)

!hide
~~~~
We need to be able to tell whether a given literal occurs somewhere inside a given clause.
For this reason we show that !ref(_IsInClause_) is decidable:

```
_isInClause?_ : (lit : Literal φ) → (C : DNFClause ψ) → Dec (lit IsInClause C)
```

The construction proceeds by scanning the clause,
as in !remoteRef(part0)(List)(_∈?_).
~~~~
~~~~
```
lit isInClause? ∅ = no λ ()

_isInClause?_ {φ} {ψ} lit (lit' ∙)
  with φ ≡? ψ
... | no φ≢ψ = no λ{stop1 → φ≢ψ refl}
Pos p isInClause? (Pos p ∙) | yes refl = yes stop1
Neg p isInClause? (Neg p ∙) | yes refl = yes stop1

_isInClause?_ {φ} {ψ ∧ ξ} lit (lit' , C)
  with φ ≡? ψ
Pos p isInClause? (Pos p , C) | yes refl = yes stop2
Neg p isInClause? (Neg p , C) | yes refl = yes stop2
lit isInClause? (lit' , C) | no φ≢ψ
  with lit isInClause? C
... | yes litInC = yes (skip litInC)
... | no ~litInC = no λ{stop2 → φ≢ψ refl; (skip litInC) → ~litInC litInC}
```
~~~~

!exercise(#exercise:litTwiceInClause)
~~~
Show that removing duplicated occurrences of the same literal preserves the semantics:

```
litTwiceInClause : (lit : Literal φ) (C : DNFClause ψ) →
  lit IsInClause C →
  ------------------
  φ ∧ ψ ⟺ ψ
```

*Hint*: Use idempotence !remoteRef(part1)(Semantics)(idempotAnd), commutativity !remoteRef(part1)(Semantics)(commAnd), and associativity !remoteRef(part1)(Semantics)(assocAnd) of conjunction.
~~~
~~~
```
litTwiceInClause {φ} lit (lit ∙) stop1 ϱ = idempotAnd φ ϱ

litTwiceInClause {φ} {φ ∧ ψ} lit (lit , C) stop2 ϱ
  rewrite sym (assocAnd φ φ ψ ϱ) |
          idempotAnd φ ϱ = refl
          
litTwiceInClause {φ} {ψ ∧ ξ} lit (lit' , C) (skip litInC) ϱ
  rewrite sym (assocAnd φ ψ ξ ϱ) |
          commAnd φ ψ ϱ |
          assocAnd ψ φ ξ ϱ |
          litTwiceInClause lit C litInC ϱ = refl
```
~~~

We are now ready to write a function which simplifies a clause by removing repeated occurrences of the same literal.
Correctness is guaranteed by !ref(litTwiceInClause):

```
simplifyDNFClause : DNFClause φ → ∃[ ψ ] DNFClause ψ × φ ⟺ ψ
simplifyDNFClause ∅ = ⊤ , ∅ , λ ϱ → refl
simplifyDNFClause (lit ∙) = _ , lit ∙ , λ ϱ → refl
simplifyDNFClause {φ ∧ ψ} (lit , C)
  with simplifyDNFClause C
... | ξ , D , ψ⟺ξ
  with lit isInClause? C
... | yes litInC = _ , D , sound where

  sound : φ ∧ ψ ⟺ ξ
  sound ϱ rewrite sym (ψ⟺ξ ϱ) = litTwiceInClause lit C litInC ϱ 

... | no ~litInC = _ , (lit , D) , sound where

  sound : φ ∧ ψ ⟺ φ ∧ ξ
  sound ϱ rewrite ψ⟺ξ ϱ = refl
```

### Case 2: Positive and negative occurrences

The second simplification regards the case when the same literal appears both positively and negatively.
We would like to concisely capture the notion of the dual of a literal.
A first attempt would be the following:

    _° : Literal φ → Literal ?
    Pos p ° = Neg p
    Neg p ° = Pos p

However it is not clear what should be the expression to fill the hole `?`.

!exercise(#exercise:dual)
~~~
Complete the definition of `_°`.
*Hint*: Can one express the formula in the hole as a function of `φ`?
~~~
~~~
We define a function that maps a proposition to its negation, and symmetrically:

```
dual : Formula → Formula
dual (` p) = ¬ ` p
dual (¬ ` p) = ` p
dual φ = φ
```

What happens to other formulas does not really matter,
and we choose not to alter them for simplicity.
We can then complete the definition of the dual literal as follows:

```
infix 25 _°
_° : Literal φ → Literal (dual φ)
Pos p ° = Neg p
Neg p ° = Pos p
```
~~~

The following binary predicate expresses the fact that a literal and its dual both appear in the same clause:

```
_andDualIsInClause_ : ∀ {φ} → Literal φ → DNFClause ψ → Set
lit andDualIsInClause C = lit IsInClause C × lit ° IsInClause C
```

!hide
~~~
First of all, we can decide whether this is the case (by scanning all literals, one at at time):

```
someLitAndDualInClause :
  (C : DNFClause φ) →
  -------------------------------------------------
  Dec (∃P[ lit ← Literal ] lit andDualIsInClause C)
```

(The `∃P`-notation is a convenient abbreviation for `∃[ ψ ] Σ (Literal ψ) λ lit → lit andDualIsInClause C`
when we do not want to explicitly mention the underlying formula `ψ`.)
~~~
~~~
```
someLitAndDualInClause ∅ = no λ{()}

-- it cannot be that lit can be both of the form Pos p and Neg p
someLitAndDualInClause (lit ∙) = no λ{(` p , Pos p , stop1 , ())}

someLitAndDualInClause (lit , C)
  with lit ° isInClause? C
... | yes proof = yes (_ , lit , stop2 , skip proof)
... | no proof
  with someLitAndDualInClause C
... | yes (_ , lit' , lit'InC , lit'°InC) = yes (_ , lit' , skip lit'InC , skip lit'°InC)
... | no proof' = no λ{
  (_ , Pos p , stop2 , skip NegpInC) → proof NegpInC;
  (_ , Neg p , stop2 , skip PospInC) → proof PospInC;
  (_ , Pos p , skip PospInC , stop2) → proof PospInC;
  (_ , Pos p , skip PospInC , skip NegpInC) → proof' (_ , Pos p , PospInC , NegpInC);
  (_ , Neg p , skip NegpInC , stop2) → proof NegpInC;
  (_ , Neg p , skip NegpInC , skip PospInC) → proof' (_ , Pos p , PospInC , NegpInC)}
```
~~~

!hide
~~~
If a clause contains a literal both positively and negatively,
then it is unsatisfiable:

```
litAndDualInClause-sound : {lit : Literal φ} {C : DNFClause ψ} →
  lit IsInClause C →
  lit ° IsInClause C →
  --------------------
  ψ ⟺ ⊥
```

The proof of is by a nested induction on the evidence that `lit` and its dual `lit °` are in `C`.
~~~
~~~
The following little fact about duals will be used several times in the proof:

```
φ∧dualφ⟺⊥ : Literal φ → φ ∧ dual φ ⟺ ⊥
φ∧dualφ⟺⊥ (Pos p) ϱ rewrite a∧𝔹¬𝔹a≡ff (ϱ p) = refl
φ∧dualφ⟺⊥ (Neg p) ϱ rewrite a∧𝔹¬𝔹a≡ff (¬𝔹 ϱ p) = refl
```

We now come to the proof of !ref(litAndDualInClause-sound).
The first base case cannot actually occur since if `C` is of the form `lit' ∙`,
then `lit'` cannot be simultaneously of the form `lit` and `lit °`:

```
litAndDualInClause-sound {lit = Pos p} stop1 ()
litAndDualInClause-sound {lit = Neg p} stop1 ()
```

In the second base case we have found the sought occurrence of `lit` in `C`.
The proof continues with a nested induction on the evidence that its dual `lit °` is in `C`
(and its occurrence is necessarily further than `lit`):

```
litAndDualInClause-sound {φ} {ψ} {lit} {C} stop2 (skip lit°InC) = go lit°InC where

  go : ∀ {ψ} {C : DNFClause ψ} → lit ° IsInClause C → φ ∧ ψ ⟺ ⊥
  go stop1 = φ∧dualφ⟺⊥ lit
  go {ψ = _ ∧ ψ} stop2 ϱ
    rewrite sym (assocAnd φ (dual φ) ψ ϱ) |
                φ∧dualφ⟺⊥ lit ϱ = refl
  go {ψ = _ ∧ ψ} (skip {ψ = φ'} lit°InC) ϱ
    with go lit°InC
  ... | φ∧ψ⟺⊥ rewrite sym (assocAnd φ φ' ψ ϱ) |
                       commAnd φ φ' ϱ |
                       assocAnd φ' φ ψ ϱ |
                       φ∧ψ⟺⊥ ϱ = refl
```

The third base case is symmetric.
We have found the occurrence of `lit °` in `C`
and we proceed by nested induction on the evidence that its dual `lit` is in `C`:

```
litAndDualInClause-sound {φ} {lit = lit} (skip litInC) stop2 = go litInC where

  go : ∀ {ψ} {C : DNFClause ψ} → lit IsInClause C → dual φ ∧ ψ ⟺ ⊥
  go stop1 ϱ rewrite commAnd (dual φ) φ ϱ = φ∧dualφ⟺⊥ lit ϱ
  go {ψ = _ ∧ ψ} stop2 ϱ
    rewrite sym (assocAnd (dual φ) φ ψ ϱ) |
            commAnd (dual φ) φ ϱ |
            φ∧dualφ⟺⊥ lit ϱ = refl
  go {ψ = _ ∧ ψ} (skip {ψ = φ'} litInC) ϱ
    with go litInC
  ... | dualφ∧ψ⟺⊥
    rewrite sym (assocAnd (dual φ) φ' ψ ϱ) |
            commAnd (dual φ) φ' ϱ |
            assocAnd φ' (dual φ) ψ ϱ |
            dualφ∧ψ⟺⊥ ϱ = refl
```

Finally, in the inductive step we know that neither `lit` nor its dual appear as the first literal in `C`,
and we can thus appeal to recursion:

```
litAndDualInClause-sound (skip litInC) (skip lit°InC) ϱ
  with litAndDualInClause-sound litInC lit°InC
... | ξ⟺⊥ rewrite ξ⟺⊥ ϱ = refl
```
~~~

### Putting things together

We are now in a position to present the core DNF-simplification procedure:

```
simplifyDNF : DNF φ → ∃[ ψ ] DNF ψ × φ ⟺ ψ
```

The construction is by induction on the evidence that `φ` is in DNF.
The first base case is easy enough to start with:

```
simplifyDNF ∅ = _ , ∅ , λ ϱ → refl
```

In the second base case the DNF consists of a single clause `C`.
We appeal to !ref(someLitAndDualInClause) to test whether `C` is unsatisfiable.
In the positive case the whole DNF reduces to `∅`,
otherwise to the simplification of `C`:

```
simplifyDNF (C ∙)
  with someLitAndDualInClause C
... | yes (_ , lit , litInC , lit°InC) = _ , ∅ , litAndDualInClause-sound litInC lit°InC
... | no _
  with simplifyDNFClause C
... | _ , D , equiv = _ , D ∙ , equiv
```

The inductive step is analogous:

```
simplifyDNF {φ ∨ ψ} (C , DNFψ)
  with simplifyDNF DNFψ
... | ψ' , DNF' , ψ⟺ψ'
  with someLitAndDualInClause C
... | yes (_ , lit , litInC , lit°InC) = ψ' , DNF' , φ∨ψ⟺ψ' where

  φ∨ψ⟺ψ' : φ ∨ ψ ⟺ ψ'
  φ∨ψ⟺ψ' ϱ
    rewrite litAndDualInClause-sound litInC lit°InC ϱ |
            ψ⟺ψ' ϱ = refl
    
... | no _
  with simplifyDNFClause C
... | φ' , D , φ⟺φ' = φ' ∨ ψ' , (D , DNF') , φ∨ψ⟺φ'∨ψ' where

  φ∨ψ⟺φ'∨ψ' : φ ∨ ψ ⟺ φ' ∨ ψ'
  φ∨ψ⟺φ'∨ψ' ϱ
    rewrite φ⟺φ' ϱ |
            ψ⟺ψ' ϱ = refl
```

## Complete transformation

The final !ref(DNF) transformation is achieved by combining the !ref(NNF) transformation,
the unsimplifying !ref(dnf1) transformation,
followed by !ref(simplifyDNF) and !remoteRef(part1)(Semantics)(simplify).
To prove its correctness we have to first show that !remoteRef(part1)(Semantics)(simplify) preserves !ref(DNF) formulas.

!exercise(#exercise:simplify-preserves-DNF)
~~~
Show that !remoteRef(part1)(Semantics)(simplify) preserves !ref(DNF) formulas:

```
simplify-preserves-DNF : DNF φ → DNF (simplify φ)
```

*Hint*: It will be convenient to first prove some auxiliary facts:

```
simplify1-preserves-Literal : Literal φ → Literal (simplify1 φ)
simplify1-preserves-DNFClause : DNFClause φ → DNFClause (simplify1 φ)
simplify1-preserves-DNF : DNF φ → DNF (simplify1 φ)

simplify-preserves-Literal : Literal φ → Literal (simplify φ)
simplify-preserves-DNFClause : DNFClause φ → DNFClause (simplify φ)
```
~~~
~~~
```
simplify1-preserves-Literal (Pos p) = Pos p
simplify1-preserves-Literal (Neg p) = Neg p
```

```
simplify1-preserves-DNFClause ∅ = ∅
simplify1-preserves-DNFClause (lit ∙) = simplify1-preserves-Literal lit ∙
simplify1-preserves-DNFClause {φ ∧ ψ} (lit , Cφ)
  with simplify1-preserves-Literal lit
... | lit'
  with simplifyView (φ ∧ ψ)
... | φ ∧⊥ = Cφ
... | φ ∧⊤ = lit ∙
... | stop _ = lit , Cφ
```

```
simplify1-preserves-DNF ∅ = ∅
simplify1-preserves-DNF (Cφ ∙) = simplify1-preserves-DNFClause Cφ ∙
simplify1-preserves-DNF {φ ∨ ψ} (Cφ , DNFψ)
  with simplify1-preserves-DNFClause Cφ 
... | Cφ'
  with simplifyView (φ ∨ ψ)
... | ⊥∨ ψ = DNFψ
... | φ ∨⊥ = Cφ ∙
... | ⊤∨ ψ = Cφ' ∙
... | φ ∨⊤ = DNFψ
... | stop _ = Cφ , DNFψ
```

```
simplify-preserves-Literal (Pos p) = Pos p
simplify-preserves-Literal (Neg p) = Neg p
```

```
simplify-preserves-DNFClause ∅ = ∅
simplify-preserves-DNFClause (lit ∙) = simplify-preserves-Literal lit ∙
simplify-preserves-DNFClause (lit , Cφ)
  with simplify-preserves-Literal lit |
       simplify-preserves-DNFClause Cφ
... | lit' | Cφ' = simplify1-preserves-DNFClause (lit' , Cφ')
```

```
simplify-preserves-DNF {⊥} ∅ = ∅
simplify-preserves-DNF {⊤} (∅ ∙) = ∅ ∙
simplify-preserves-DNF {` p} ((Pos p ∙) ∙) = (Pos p ∙) ∙
simplify-preserves-DNF {¬ (` p)} ((Neg p ∙) ∙) = (Neg p ∙) ∙
simplify-preserves-DNF (Cφ ∙)
  with simplify-preserves-DNFClause Cφ
... | res = res ∙
simplify-preserves-DNF {φ ∨ ψ} (Cφ , DNFφ)
  with simplify-preserves-DNFClause Cφ |
       simplify-preserves-DNF DNFφ
... | res0 | res1 = simplify1-preserves-DNF (res0 , res1)
```
~~~

The announced !ref(DNF) transformation follows:

```
dnf : ∀ φ → ∃[ ψ ] DNF ψ × φ ⟺ ψ
dnf φ
  with nnf φ | nnf-NNF φ | nnf-sound φ
... | φ' | NNFφ' | φ⟺φ'
  with dnf1 NNFφ'
... | ψ , DNFψ , φ'⟺ψ
  with simplifyDNF DNFψ
... | ψ' , DNFψ' , ψ⟺ψ'
  with inspect (simplify ψ')
... | it ψ'' eq
  with simplify-preserves-DNF DNFψ'
... | DNFψ'' rewrite eq = ψ'' , DNFψ'' , φ⟺ψ'' where

  φ⟺ψ'' : φ ⟺ ψ''
  φ⟺ψ'' ϱ rewrite φ⟺φ' ϱ |
                  φ'⟺ψ ϱ |
                  ψ⟺ψ' ϱ |
                  sym ((simplify-sound ψ') ϱ) |
                  eq = refl 
```

For example,

```
_ : dfst (dnf (⊥ ∧ ` p₀)) ≡ ⊥    ×
    dfst (dnf (⊤ ∨ ` p₀)) ≡ ⊤    ×
    dfst (dnf (⊤ ∧ ` p₀ ∧ ` p₀)) ≡ ` p₀ ×
    dfst (dnf (` p₀ ∧ (` p₁ ∨ ¬ ` p₀))) ≡ ` p₀ ∧ ` p₁

_ = refl , refl , refl , refl
```

## Applications

!exercise(#exercise:satisfiability)
~~~
What is the complexity of checking satisfiability of a formula in !ref(DNF)?
And tautology?
~~~
~~~

~~~

# Conjunctive normal form {#CNF}

A (CNF) *clause* `C` is a disjunction of literals `l1 ∨ ⋯ ∨ lm`
and a formula is in *conjunctive normal form* (CNF) if it is a conjunction of clauses `C1 ∧ ⋯ ∧ Cn`:

```
data CNFClause : Formula → Set where
  ∅ : CNFClause ⊥
  _∙ : Literal φ → CNFClause φ
  _,_ : Literal φ → CNFClause ψ → CNFClause (φ ∨ ψ)

data CNF : Formula → Set where
  ∅ : CNF ⊤
  _∙ : CNFClause φ → CNF φ
  _,_ : CNFClause φ → CNF ψ → CNF (φ ∧ ψ)
```

!exercise(#exercise:DNF-CNF-duality)
~~~
Show that the conjunctive normal form (CNF) is [*dual*](../../part1/Semantics#duality) to the disjunctive normal form from the [previous section](#CNF),
in the sense that swapping conjunctions with disjunctions allows one to pass from one form to the other:

```
DNF-CNF-dual : DNF φ → CNF (φ ⁻)
```
~~~
~~~
```
literal-dual : Literal φ → Literal (φ ⁻)
literal-dual (Pos p) = Pos p
literal-dual (Neg p) = Neg p
```
```
DNF-CNF-clause-dual : DNFClause φ → CNFClause (φ ⁻)
DNF-CNF-clause-dual ∅ = ∅
DNF-CNF-clause-dual (l ∙) = literal-dual l ∙
DNF-CNF-clause-dual (l , C) = literal-dual l , DNF-CNF-clause-dual C
```
```
DNF-CNF-dual ∅ = ∅
DNF-CNF-dual (C ∙) = DNF-CNF-clause-dual C ∙
DNF-CNF-dual (C , D) = DNF-CNF-clause-dual C , DNF-CNF-dual D
```
~~~

Duality is a very useful property since it allows us to "recycle" the !ref(DNF) transformation from the previous section into a !ref!(CNF) transformation.

```
Literal-Formula[⊥,⊤,¬,∨,∧] : Literal φ → Formula[⊥,⊤,¬,∨,∧] φ
Literal-Formula[⊥,⊤,¬,∨,∧] (Pos p) = ` p
Literal-Formula[⊥,⊤,¬,∨,∧] (Neg p) = ¬ ` p

DNFClause-Formula[⊥,⊤,¬,∨,∧] : DNFClause φ → Formula[⊥,⊤,¬,∨,∧] φ
DNFClause-Formula[⊥,⊤,¬,∨,∧] ∅ = ⊤
DNFClause-Formula[⊥,⊤,¬,∨,∧] (l ∙) = Literal-Formula[⊥,⊤,¬,∨,∧] l
DNFClause-Formula[⊥,⊤,¬,∨,∧] (l , C)
  = Literal-Formula[⊥,⊤,¬,∨,∧] l ∧ DNFClause-Formula[⊥,⊤,¬,∨,∧] C

DNF-Formula[⊥,⊤,¬,∨,∧] : DNF φ → Formula[⊥,⊤,¬,∨,∧] φ
DNF-Formula[⊥,⊤,¬,∨,∧] ∅ = ⊥
DNF-Formula[⊥,⊤,¬,∨,∧] (C ∙) = DNFClause-Formula[⊥,⊤,¬,∨,∧] C
DNF-Formula[⊥,⊤,¬,∨,∧] (C , D)
  =  DNFClause-Formula[⊥,⊤,¬,∨,∧] C ∨ DNF-Formula[⊥,⊤,¬,∨,∧] D

NNF-Formula[⊥,⊤,¬,∨,∧] : NNF φ → Formula[⊥,⊤,¬,∨,∧] φ
NNF-Formula[⊥,⊤,¬,∨,∧] ⊤ = ⊤
NNF-Formula[⊥,⊤,¬,∨,∧] ⊥ = ⊥
NNF-Formula[⊥,⊤,¬,∨,∧] (` p) = ` p
NNF-Formula[⊥,⊤,¬,∨,∧] (¬` p) = ¬ ` p
NNF-Formula[⊥,⊤,¬,∨,∧] (φ ∧ ψ) = NNF-Formula[⊥,⊤,¬,∨,∧] φ ∧ NNF-Formula[⊥,⊤,¬,∨,∧] ψ
NNF-Formula[⊥,⊤,¬,∨,∧] (φ ∨ ψ) = NNF-Formula[⊥,⊤,¬,∨,∧] φ ∨ NNF-Formula[⊥,⊤,¬,∨,∧] ψ

cnf : ∀ φ → ∃[ ψ ] CNF ψ × φ ⟺ ψ
cnf φ
  with nnf φ | nnf-NNF φ | nnf-sound φ
... | φ' | NNFφ' | φ⟺φ'
  with dnf (φ' ⁻)
... | ψ , DNFψ , φ'⁻⟺ψ = ψ ⁻ , DNF-CNF-dual DNFψ , φ⟺ψ⁻ where

    Fψ : Formula[⊥,⊤,¬,∨,∧] ψ
    Fψ = DNF-Formula[⊥,⊤,¬,∨,∧] DNFψ

    Fφ' : Formula[⊥,⊤,¬,∨,∧] φ'
    Fφ' = NNF-Formula[⊥,⊤,¬,∨,∧] NNFφ'
    
    Fφ'⁻ : Formula[⊥,⊤,¬,∨,∧] (φ' ⁻)
    Fφ'⁻ = dual-preservation Fφ'

    φ'⁻⁻⟺ψ⁻ : φ' ⁻ ⁻ ⟺ ψ ⁻
    φ'⁻⁻⟺ψ⁻ = duality-equivalence-1 Fφ'⁻ Fψ φ'⁻⟺ψ

    φ'⟺ψ⁻ : φ' ⟺ ψ ⁻
    φ'⟺ψ⁻ rewrite sym (dual-involutive Fφ') = φ'⁻⁻⟺ψ⁻

    φ⟺ψ⁻ : φ ⟺ ψ ⁻
    φ⟺ψ⁻ ϱ rewrite φ⟺φ' ϱ |
                   φ'⟺ψ⁻ ϱ = refl
```

For example,

```
_ : dfst (cnf (⊥ ∧ ` p₀)) ≡ ⊥    ×
    dfst (cnf (⊤ ∨ ` p₀)) ≡ ⊤    ×
    dfst (cnf (⊤ ∧ ` p₀ ∧ ` p₀)) ≡ ` p₀ ∧ ` p₀  ×
    dfst (cnf (` p₀ ∧ (` p₁ ∨ ¬ ` p₀))) ≡ ` p₀ ∧ (` p₁ ∨ ¬ ` p₀) ×
    dfst (cnf (` p₀ ∨ (` p₁ ∧ ¬ ` p₀))) ≡ ` p₀ ∨ ` p₁

_ = refl , refl , refl , refl , refl
```
