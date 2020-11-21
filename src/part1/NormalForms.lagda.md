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

infix 99 ¬`_
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
          
_+∨+_ : DNF φ →
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
_+∨+_ {⊥} {ψ} ∅ DNFψ = ψ , DNFψ , correctness where

  correctness : ⊥ ∨ ψ ⟺ ψ
  correctness ϱ with ⟦ ψ ⟧ ϱ
  ... | tt = refl
  ... | ff = refl

_+∨+_ {φ} {ψ} (Cφ ∙) DNFψ = φ ∨ ψ , (Cφ , DNFψ) , λ ϱ → refl

_+∨+_ {φ ∨ ψ} {ξ} (Cφ , DNFψ) DNFξ
  with DNFψ +∨+ DNFξ
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
  with DNFξ +∨+ DNFη
... | μ , DNFμ , ξ∨η⟺μ = μ , DNFμ , correctness where

  correctness : (φ ∨ φ') ∧ ψ ⟺ μ
  correctness ϱ rewrite
    distrAndOr-right φ φ' ψ ϱ |
    φ'∧ψ⟺η ϱ |
    φ∧ψ⟺ξ ϱ |
    ξ∨η⟺μ ϱ = refl
```

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
Disjunctions are easy since DNF formulas are closed under disjunction, with no blowup (c.f. !ref(_+∨+_)):

```
dnf1 {φ ∨ ψ} (NNFφ ∨ NNFψ)
  with dnf1 NNFφ          | dnf1 NNFψ
... | φ' , DNFφ' , φ⟺φ' | ψ' , DNFψ' , ψ⟺ψ'
  with DNFφ' +∨+ DNFψ'
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
_ : dfst (dnf1 (⊥ ∧ ` p₀)) ≡ ⊥        ×
    dfst (dnf1 (⊤ ∨ ` p₀)) ≡ ⊤ ∨ ` p₀ ×
    dfst (dnf1 (⊤ ∧ ` p₀)) ≡ ` p₀     ×
    dfst (dnf1 (` p₀ ∧ (` p₁ ∨ ¬` p₀))) ≡ ` p₀ ∧ ` p₁ ∨ ` p₀ ∧ ¬ ` p₀

_ = refl , refl , refl , refl
```

We can see that !ref(dnf1) performs some rudimentary form of simplification, e.g., by removing `⊥` in ``⊥ ∧ ` p₀``,
but not all the simplifications we may desire.
For instance ``⊤ ∨ ` p₀`` should be transformed into `⊤` (which could be achieved by !remoteRef(part1)(Semantics)(simplify))
but more significantly `` ` p₀ ∧ ` p₁ ∨ ` p₀ ∧ ¬ ` p₀ ``
should be transformed to `` ` p₀ ∧ ` p₁ `` by removing the unsatisfiable clause `` ` p₀ ∧ ¬ ` p₀ ``.
The latter kind of simplification is more specific to the DNF form, and will be handled in the next section.

## Simplification

The !ref(DNF) structure allows us to simplify formulas to a stronger extend that what is possible with the generic procedure !remoteRef(part1)(Semantics)(simplify).

```
dual : Formula → Formula
dual (` p) = ¬ ` p
dual (¬ ` p) = ` p
dual φ = φ

infix 25 _°
_° : Literal φ → Literal (dual φ)
Pos p ° = Neg p
Neg p ° = Pos p

infix 10 _IsInClause_
data _IsInClause_ : Literal φ → DNFClause ψ → Set where
  stop1 : ∀ {lit : Literal φ} → lit IsInClause (lit ∙)
  stop2 : ∀ {lit : Literal φ} {C : DNFClause ψ} → lit IsInClause (lit , C)
  skip : ∀ {lit : Literal φ} {lit' : Literal ψ} {C : DNFClause ξ} → lit IsInClause C → lit IsInClause (lit' , C)
  
_isInClause?_ : (lit : Literal φ) → (C : DNFClause ψ) → Dec (lit IsInClause C)

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

litAndDualInClause : (lit : Literal φ) (C : DNFClause ψ) →
  lit IsInClause C →
  lit ° IsInClause C →
  --------------------
  ψ ⟺ ⊥

litAndDualInClause lit C litInC lit°InC = {!!}

simplifyDNFClause : DNFClause φ → ∃[ ψ ] DNFClause ψ × φ ⟺ ψ
simplifyDNFClause ∅ = ⊤ , ∅ , λ ϱ → refl
simplifyDNFClause (lit ∙) = _ , lit ∙ , λ ϱ → refl
simplifyDNFClause (lit , C)
  with lit isInClause? C  
... | yes litInC = {!!}
... | no ~litInC = {!!}
  

-- DNFsimplify1 : DNF φ → 
```


## Complete transformation

The final !ref(DNF) transformation is achieved

# Conjunctive normal form {#CNF}

CNF is dual to DNF.
Is the exponential CNF transformation useful anywhere?

```
data CNFClause : Formula → Set where
  ∅ : CNFClause ⊥
  _,_ : ∀ {φ ψ} → Literal φ → CNFClause ψ → CNFClause (φ ∨ ψ)

data CNF : Formula → Set where
  ∅ : CNF ⊤
  _,_ : ∀ {φ ψ} → CNFClause φ → CNF ψ → CNF (φ ∧ ψ)
```
