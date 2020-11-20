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
    φ ψ : Formula
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
which we can automaticalally check thanks to !ref(WNNF?):

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

The proof of soundess is conceptually simple and it is based on the double negation and de Morgan's laws.
The only difficulty is posed by the termination checker.

The most immediate way to prove soundness would be to mimick the recursive structure of !ref(wnnf) as follows:

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
wereby the termination checker will complain about the recursive invocation marked by `(*)` above.
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

where `a` and `b` are integer parameter whose values have to be found.
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

The worst case of the !ref(WNNF) translation is achieved when a single negation is pushed inside a formula of size `2*n` the form `` ¬ (` p₁ ∨ ⋯ ∨ ` pₙ) ``,
yielding a !ref(WNNF) formula `` ¬ ` p₁ ∨ ⋯ ∨ ¬ ` pₙ `` of size `3*n-1`.
Notice that the bound given by !ref(wnnf-size-¬) in this case would be `4*n`,
which thus is not tight in general.

# Negation normal form {#NNF}

A propositional formula `φ` is in *negation normal form* (NNF) if it uses only the connectives
!remoteRef(part1)(Semantics)(Formula)(⊥),
!remoteRef(part1)(Semantics)(Formula)(⊤),
!remoteRef(part1)(Semantics)(Formula)(¬_),
!remoteRef(part1)(Semantics)(Formula)(_∨_), and
!remoteRef(part1)(Semantics)(Formula)(_∧_),
and negation appears only in front of propositional variables, i.e., inside literals.
In particular, a NNF formula does not contain the implication `⇒` and bi-implication `⇔` connectives.
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

Given a formula `φ`, we can decide whether it is in NNF or not:

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
--ψ₀ ψ₁ ψ₂ ψ₃ ψ₄ ψ₅ : Formula
```

::::::::::::: {.inlinecode}

For instance, the formulas
```
--ψ₀ = ⊤
```
,
```
--ψ₁ = ¬ ` p₀ ∨ ` p₁
```
, and
```
--ψ₂ = ¬ ` p₀ ∧ (` p₁ ∨ ¬ ` p₂)
```
are in NNF, while
```
--ψ₃ = ¬ ⊤
```
,
```
--ψ₄ = ¬ ¬ ` p₀
```
, and
```
--ψ₅ = ¬ (` p₀ ∨ ` p₁)
```
are not, as we automatically check:

:::::::::::::

```
--_ : All? NNF? ([ ψ₀ ψ₁ ψ₂ ]) ×? All? (~?_ ∘ NNF?) ([ ψ₃ ψ₄ ψ₅ ]) ≡ yes _
--_ = refl
```

## Remove implications and bi-implications

```
removeImp : Formula → Formula
removeImp ⊥ = ⊥
removeImp ⊤ = ⊤
removeImp (` p) = ` p
removeImp (¬ φ) = ¬ removeImp φ
removeImp (φ ∨ ψ) = removeImp φ ∨ removeImp ψ
removeImp (φ ∧ ψ) = removeImp φ ∧ removeImp ψ
removeImp (φ ⇒ ψ) = ¬ removeImp φ ∨ removeImp ψ
removeImp (φ ⇔ ψ) with φ́ ← removeImp φ | ψ́ ← removeImp ψ
  = (¬ φ́ ∨ ψ́) ∧ (φ́ ∨ ¬ ψ́)

removeImp-sound : ∀ φ → φ ⟺ removeImp φ
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

removeImp-impFree : ∀ φ → Formula[⊥,⊤,¬,∨,∧] (removeImp φ)
removeImp-impFree ⊥ = ⊥
removeImp-impFree ⊤ = ⊤
removeImp-impFree (` p) = ` p
removeImp-impFree (¬ φ) = ¬ removeImp-impFree φ
removeImp-impFree (φ ∨ ψ) = removeImp-impFree φ ∨ removeImp-impFree ψ
removeImp-impFree (φ ∧ ψ) = removeImp-impFree φ ∧ removeImp-impFree ψ
removeImp-impFree (φ ⇒ ψ) = (¬ removeImp-impFree φ) ∨ removeImp-impFree ψ
removeImp-impFree (φ ⇔ ψ) = ((¬ removeImp-impFree φ) ∨ removeImp-impFree ψ) ∧
                              (removeImp-impFree φ ∨ (¬ removeImp-impFree ψ))
```

## Transformation to NNF

```
nnf : Formula → Formula
nnf = wnnf ∘ removeImp ∘ simplify
```

Example:

```
_ : nnf (¬ ¬ (` p₀ ⇒ ¬ (` p₁ ∧ ` p₂ ∧ ⊤))) ≡ ¬ ` p₀ ∨ ¬ ` p₁ ∨ ¬ ` p₂
_ = refl 
```

## Correctness

### Structure

```
wnnf-impFree : ∀ φ → Formula[⊥,⊤,¬,∨,∧] φ → NNF (wnnf φ)
wnnf-impFree ⊥ ⊥ = ⊥
wnnf-impFree ⊤ ⊤ = ⊤
wnnf-impFree (` p) (` p) = ` p
wnnf-impFree (¬ _) (¬ ⊥) = ⊤
wnnf-impFree (¬ _) (¬ ⊤) = ⊥
wnnf-impFree (¬ _) (¬ (` p)) = ¬` p
wnnf-impFree (¬ ¬ φ) (¬ ¬ view-φ) = wnnf-impFree φ view-φ
wnnf-impFree (¬ (φ ∨ ψ)) (¬ (view-φ ∨ view-ψ)) = wnnf-impFree (¬ φ) (¬ view-φ) ∧ wnnf-impFree (¬ ψ) (¬ view-ψ)
wnnf-impFree (¬ (φ ∧ ψ)) (¬ (view-φ ∧ view-ψ)) = wnnf-impFree (¬ φ) (¬ view-φ) ∨ wnnf-impFree (¬ ψ) (¬ view-ψ)
wnnf-impFree (φ ∨ ψ) (view-φ ∨ view-ψ) = wnnf-impFree φ view-φ ∨ wnnf-impFree ψ view-ψ
wnnf-impFree (φ ∧ ψ) (view-φ ∧ view-ψ) = wnnf-impFree φ view-φ ∧ wnnf-impFree ψ view-ψ

nnf-NNF : ∀ φ → NNF (nnf φ)
nnf-NNF φ = wnnf-impFree (removeImp (simplify φ)) (removeImp-impFree (simplify φ))
```

### Soundness

```
nnf-sound : ∀ φ → φ ⟺ nnf φ
nnf-sound φ ϱ
  rewrite sym (wnnf-sound (removeImp (simplify φ)) ϱ) |
          sym (removeImp-sound (simplify φ) ϱ) |
          sym (simplify-sound φ ϱ) = refl
```


# Disjunctive normal form {#DNF}

A *clause* `C` is a conjunction of literals `l1 ∧ ⋯ ∧ lm`.
A formula is in  *disjunctive normal form* (DNF) if it is a disjunction of clauses `C1 ∨ ⋯ ∨ Cn`.

```
data Literal : Formula → Set where
  Pos : (p : PropName) → Literal (` p)
  Neg : (p : PropName) → Literal (¬ (` p))
  
data DNFClause : Formula → Set where
  ∅ : DNFClause ⊤
  _,_ : ∀ {φ ψ} → Literal φ → DNFClause ψ → DNFClause (φ ∧ ψ)

data DNF : Formula  → Set where
  ∅ : DNF ⊥
  _,_ : ∀ {φ ψ} → DNFClause φ → DNF ψ → DNF (φ ∨ ψ)
```

We warm up and show how we can merge two clauses while preserving the semantics.
This is essentially list concatenation, with additional code showing that it is semantics-preserving for formulas.

```
merge : ∀ {φ ψ} → DNFClause φ → DNFClause ψ → ∃[ ξ ] DNFClause ξ × ξ ⟺ φ ∧ ψ
merge {⊤} {ψ} ∅ Cψ = ψ , Cψ , correctness where

  correctness : ψ ⟺ ⊤ ∧ ψ
  correctness ρ with ⟦ ψ ⟧ ρ
  ... | tt = refl
  ... | ff = refl
  
merge {φ ∧ φ'} {ψ} (Lφ , Cφ') Cψ with merge Cφ' Cψ
... | ξ , Cξ , ξ⟺φ'∧ψ = φ ∧ ξ , (Lφ , Cξ) , correctness where

  correctness : φ ∧ ξ ⟺ (φ ∧ φ') ∧ ψ
  correctness ρ rewrite ξ⟺φ'∧ψ ρ = sym (assoc-∧𝔹 _ _ _)
```

## Case 1: DNF of a disjunction

```
DNF-∨ : ∀ {φ ψ} → DNF φ → DNF ψ → ∃[ ξ ] DNF ξ × ξ ⟺ φ ∨ ψ

DNF-∨ {⊥} {ψ} ∅ DNFψ = ψ , DNFψ , correctness where

  correctness : ψ ⟺ ⊥ ∨ ψ
  correctness ρ with ⟦ ψ ⟧ ρ
  ... | tt = refl
  ... | ff = refl

DNF-∨ {φ ∨ ψ} {ξ} (Cφ , DNFψ) DNFξ with DNF-∨ DNFψ DNFξ
... | η , DNFη , η⟺ψ∨ξ = φ ∨ η , (Cφ , DNFη) , correctness where

  correctness : φ ∨ η ⟺ (φ ∨ ψ) ∨ ξ 
  correctness ρ rewrite η⟺ψ∨ξ ρ = sym (assoc-∨𝔹 _ _ _)
```

## Case 2: DNF of a conjunction

* We first show how to add a single clause.

```
DNF-∧-DNFClause : ∀ {φ ψ} → DNFClause φ → DNF ψ → ∃[ ξ ] DNF ξ × ξ ⟺ φ ∧ ψ
DNF-∧-DNFClause {φ} {⊥} Cφ ∅ =  ⊥ , ∅ , correctness where

  correctness : ⊥ ⟺ φ ∧ ⊥
  correctness ρ with ⟦ φ ⟧ ρ
  ... | tt = refl
  ... | ff = refl
  
DNF-∧-DNFClause {φ} {ψ ∨ ξ} Cφ (Cψ , DNFξ) with merge Cφ Cψ
... | φψ , Cφψ , φψ⟺φ∧ψ with DNF-∧-DNFClause Cφ DNFξ
... | η , DNFη , η⟺φ∧ξ = φψ ∨ η , (Cφψ , DNFη) , correctness where

  correctness : φψ ∨ η ⟺ φ ∧ (ψ ∨ ξ) -- crucial use of distributivity goes here
  correctness ρ rewrite φψ⟺φ∧ψ ρ | η⟺φ∧ξ ρ = sym (distr-left-∧∨𝔹 _ _ _)
```

* We now show how to distribute.

```
DNF-∧ : ∀ {φ ψ} → DNF φ → DNF ψ → ∃[ ξ ] DNF ξ × ξ ⟺ φ ∧ ψ
DNF-∧ {⊥} {ψ} ∅ DNFψ = ⊥ , ∅ , correctness where

  correctness : ⊥ ⟺ ⊥ ∧ ψ
  correctness ρ = refl
  
DNF-∧ {φ ∨ φ'} {ψ} (Cφ , DNFφ') DNFψ with DNF-∧-DNFClause Cφ DNFψ | DNF-∧ DNFφ' DNFψ
... | ξ , DNFξ , ξ⟺φ∧ψ | η , DNFη , η⟺φ'∧ψ with DNF-∨ DNFξ DNFη
... | μ , DNFμ , μ⟺ξ∨η = μ , DNFμ , correctness where

  correctness : μ ⟺ (φ ∨ φ') ∧ ψ
  correctness ρ rewrite μ⟺ξ∨η ρ | η⟺φ'∧ψ ρ | ξ⟺φ∧ψ ρ = sym (distr-right-∧∨𝔹 _ _ _)
```

We show that every formula of classical propositional logic can be transformed into an equivalent DNF formula.
We assume an input in NNF.

```
dnf : ∀ {φ} → NNF φ → ∃[ ψ ] DNF ψ × ψ ⟺ φ
dnf ⊤ = ⊤ ∨ ⊥ , (∅ , ∅) , correctness where

  correctness : ⊤ ∨ ⊥ ⟺ ⊤
  correctness ρ = refl
  
dnf ⊥ = ⊥ , ∅ , correctness where

  correctness : ⊥ ⟺ ⊥
  correctness ρ = refl
  
dnf (` p) = ` p ∧ ⊤ ∨ ⊥ , ((Pos p , ∅) , ∅) , correctness where

  correctness : ` p ∧ ⊤ ∨ ⊥ ⟺ ` p
  correctness ρ with ρ p
  ... | tt = refl
  ... | ff = refl
  
dnf (¬` p) = ¬ ` p ∧ ⊤ ∨ ⊥ , ((Neg p , ∅) , ∅) , correctness where

  correctness : ¬ ` p ∧ ⊤ ∨ ⊥ ⟺ ¬ ` p
  correctness ρ with ρ p
  ... | tt = refl
  ... | ff = refl

dnf {φ ∧ ψ} (NNFφ ∧ NNFψ) with dnf NNFφ | dnf NNFψ
... | φ' , DNFφ' , φ'⟺φ | ψ' , DNFψ' , ψ'⟺ψ with DNF-∧ DNFφ' DNFψ'
... | ξ , DNFξ , ξ⟺φ'∧ψ' = ξ , DNFξ , correctness where

  correctness : ξ ⟺ φ ∧ ψ
  correctness ρ rewrite ξ⟺φ'∧ψ' ρ | φ'⟺φ ρ | ψ'⟺ψ ρ = refl

dnf {φ ∨ ψ} (NNFφ ∨ NNFψ) with dnf NNFφ | dnf NNFψ
... | φ' , DNFφ' , φ'⟺φ | ψ' , DNFψ' , ψ'⟺ψ with DNF-∨ DNFφ' DNFψ'
... | ξ , DNFξ , ξ⟺φ'∨ψ' = ξ , DNFξ , correctness where

  correctness : ξ ⟺ φ ∨ ψ
  correctness ρ rewrite ξ⟺φ'∨ψ' ρ | φ'⟺φ ρ | ψ'⟺ψ ρ = refl
```

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
