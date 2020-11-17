---
title: Normal forms
---

```
{-# OPTIONS --allow-unsolved-metas #-}
open import part0.index

module part1.NormalForms (n : ℕ) where
open import part1.Semantics n hiding (∅)
```

In this chapter we study normal forms for classical propositional logic, namely

* [negation normal form (NNF)](#NNF) and its extension [ENNF](#ENNF),
* [disjunctive normal form (DNF)](#DNF), and its dual
* [conjunctive normal form (CNF)](#CNF).

# Negation normal form {#NNF}

A *literal* is either a propositional variable `p` (positive literal)
or a negation `¬ p` thereof (negated literal).
A propositional formula `φ` is in *negation normal form* (NNF)
if negation appears only in front of propositional variables, i.e., inside literals.
Since negation is implicitly present in implication `⇒` and bi-implication `⇔`,
those are forbidden too.
This is captured by the following definition:

```
data NNF : Formula → Set where
  ⊤ : NNF ⊤
  ⊥ : NNF ⊥
  `_ : (p : PropName) → NNF (` p)
  ¬`_ : (p : PropName) → NNF (¬ ` p)
  _∧_ : ∀ {φ ψ} → NNF φ → NNF ψ → NNF (φ ∧ ψ)
  _∨_ : ∀ {φ ψ} → NNF φ → NNF ψ → NNF (φ ∨ ψ)
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
ψ₀ ψ₁ ψ₂ ψ₃ ψ₄ ψ₅ : Formula
```

::::::::::::: {.inlinecode}

Thanks of decidability of !ref(NNF),
we can automatically check that 
```
ψ₀ = ⊤
```
,
```
ψ₁ = ¬ ` p₀ ∨ ` p₁
```
, and
```
ψ₂ = ¬ ` p₀ ∧ (` p₁ ∨ ¬ ` p₂)
```
are in NNF, while
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
are not:

:::::::::::::

```
_ : All? NNF? ([ ψ₀ ψ₁ ψ₂ ]) ×? All? (~?_ ∘ NNF?) ([ ψ₃ ψ₄ ψ₅ ]) ≡ yes _
_ = refl
```


Transformation to NNF and its correctness proof.

In order to avoid a termination issue,
we use two mutually recursive functions [`nnf`](#nnf) and [`nnf¬`](#nnf¬)

```
nnf : ∀ (φ : Formula) → Σ Formula λ ψ → NNF ψ × φ ⟺ ψ
nnf¬ : ∀ (φ : Formula) → Σ Formula λ ψ → NNF ψ × ¬ φ ⟺ ψ

nnf ⊤ = ⊤ , ⊤ , λ ρ → refl 
nnf ⊥ =  ⊥  , ⊥ , λ ρ → refl 
nnf (` x) = ` x , ` x , λ ρ → refl
nnf (¬ φ) = nnf¬ φ

nnf (φ ∧ ψ) with nnf φ | nnf ψ
... | nnfφ , NNFφ , φ⟺nnfφ
    | nnfψ , NNFψ , ψ⟺nnfψ = nnfφ ∧ nnfψ , NNFφ ∧ NNFψ , correctness where

    correctness : φ ∧ ψ ⟺ nnfφ ∧ nnfψ
    correctness ρ = cong2 _∧𝔹_ (φ⟺nnfφ ρ) (ψ⟺nnfψ ρ)

nnf (φ ∨ ψ) with nnf φ | nnf ψ
... | nnfφ , NNFφ , φ⟺nnfφ
    | nnfψ , NNFψ , ψ⟺nnfψ = nnfφ ∨ nnfψ , NNFφ ∨ NNFψ , correctness where

    correctness : φ ∨ ψ ⟺ nnfφ ∨ nnfψ
    correctness ρ = cong2 _∨𝔹_ (φ⟺nnfφ ρ) (ψ⟺nnfψ ρ)

nnf (φ ⇒ ψ) with nnf¬ φ | nnf ψ
... | nnf¬φ , NNF¬φ , ¬φ⟺nnf¬φ
    | nnfψ , NNFψ , ψ⟺nnfψ = nnf¬φ ∨ nnfψ , NNF¬φ ∨ NNFψ , correctness where

    correctness : φ ⇒ ψ ⟺ nnf¬φ ∨ nnfψ
    correctness ρ = begin
      ⟦ φ ⇒ ψ ⟧ ρ ≡⟨ semantics⇒𝔹 _ _ ⟩
      ⟦ ¬ φ ∨ ψ ⟧ ρ ≡⟨ cong2 _∨𝔹_ (¬φ⟺nnf¬φ ρ) (ψ⟺nnfψ ρ) ⟩
      ⟦ nnf¬φ ∨ nnfψ ⟧ ρ ∎

nnf (φ ⇔ ψ) with nnf φ | nnf¬ φ | nnf ψ | nnf¬ ψ
... | nnfφ , NNFφ , φ⟺nnfφ
    | nnf¬φ , NNF¬φ , ¬φ⟺nnf¬φ
    | nnfψ , NNFψ , ψ⟺nnfψ
    | nnf¬ψ , NNF¬ψ , ¬ψ⟺nnf¬ψ =  (nnf¬φ ∨ nnfψ) ∧ (nnfφ ∨ nnf¬ψ) , (NNF¬φ ∨ NNFψ) ∧ (NNFφ ∨ NNF¬ψ) , correctness where

    correctness : φ ⇔ ψ ⟺ (nnf¬φ ∨ nnfψ) ∧ (nnfφ ∨ nnf¬ψ)
    correctness ρ = begin
      ⟦ φ ⇔ ψ ⟧ ρ ≡⟨ semantics⇔𝔹 _ _ ⟩
      ⟦ (¬ φ ∨ ψ) ∧ (φ ∨ ¬ ψ) ⟧ ρ ≡⟨ cong2 _∧𝔹_ (cong2 _∨𝔹_ (¬φ⟺nnf¬φ ρ) (ψ⟺nnfψ ρ)) (cong2 _∨𝔹_ (φ⟺nnfφ ρ) (¬ψ⟺nnf¬ψ ρ)) ⟩
      ⟦ (nnf¬φ ∨ nnfψ) ∧ (nnfφ ∨ nnf¬ψ) ⟧ ρ ∎
```



```
nnf¬ ⊤ =  ⊥ , ⊥ , λ ρ → refl
nnf¬ ⊥ =  ⊤ , ⊤ , λ ρ → refl
nnf¬ (` p) =  ¬ ` p , ¬` p , λ ρ → refl

nnf¬ (¬ φ) with nnf φ
... | nnfφ , NNFnnfφ , φ⟺nnfφ = nnfφ , NNFnnfφ , correctness where

  correctness : ¬ ¬ φ ⟺ nnfφ
  correctness ρ = begin
    ⟦ ¬ ¬ φ ⟧ ρ ≡⟨ doubleNegationLaw φ ρ ⟩
    ⟦ φ ⟧ ρ ≡⟨ φ⟺nnfφ ρ ⟩
    ⟦ nnfφ ⟧ ρ ∎

nnf¬ (φ ∧ ψ) with nnf¬ φ | nnf¬ ψ
... | nnf¬φ , NNF¬φ , ¬φ⟺nnf¬φ
    | nnf¬ψ , NNF¬ψ , ¬ψ⟺nnf¬ψ = nnf¬φ ∨ nnf¬ψ , NNF¬φ ∨ NNF¬ψ , correctness where

    correctness : ¬ (φ ∧ ψ) ⟺ nnf¬φ ∨ nnf¬ψ
    correctness ρ = begin
      ⟦ ¬ (φ ∧ ψ) ⟧ ρ ≡⟨ deMorganAnd φ ψ ρ ⟩
      ⟦ ¬ φ ∨ ¬ ψ ⟧ ρ ≡⟨⟩
      ⟦ ¬ φ ⟧ ρ ∨𝔹 ⟦ ¬ ψ ⟧ ρ ≡⟨ cong2 _∨𝔹_ (¬φ⟺nnf¬φ ρ) (¬ψ⟺nnf¬ψ ρ) ⟩
      ⟦ nnf¬φ ⟧ ρ ∨𝔹 ⟦ nnf¬ψ ⟧ ρ ≡⟨⟩
      ⟦ nnf¬φ ∨ nnf¬ψ ⟧ ρ ∎

nnf¬ (φ ∨ ψ) with nnf¬ φ | nnf¬ ψ
... | nnf¬φ , NNF¬φ , ¬φ⟺nnf¬φ
    | nnf¬ψ , NNF¬ψ , ¬ψ⟺nnf¬ψ = nnf¬φ ∧ nnf¬ψ , NNF¬φ ∧ NNF¬ψ , correctness where

    correctness : ¬ (φ ∨ ψ) ⟺ nnf¬φ ∧ nnf¬ψ
    correctness ρ = begin
      ⟦ ¬ (φ ∨ ψ) ⟧ ρ ≡⟨ deMorganOr φ ψ ρ ⟩
      ⟦ ¬ φ ∧ ¬ ψ ⟧ ρ ≡⟨⟩
      ⟦ ¬ φ ⟧ ρ ∧𝔹 ⟦ ¬ ψ ⟧ ρ ≡⟨ cong2 _∧𝔹_ (¬φ⟺nnf¬φ ρ) (¬ψ⟺nnf¬ψ ρ) ⟩
      ⟦ nnf¬φ ⟧ ρ ∧𝔹 ⟦ nnf¬ψ ⟧ ρ ≡⟨⟩
      ⟦ nnf¬φ ∧ nnf¬ψ ⟧ ρ ∎

nnf¬ (φ ⇒ ψ) with nnf φ | nnf¬ ψ
... | nnfφ , NNFφ , φ⟺nnfφ
    | nnf¬ψ , NNF¬ψ , ¬ψ⟺nnf¬ψ = nnfφ ∧ nnf¬ψ , NNFφ ∧ NNF¬ψ , correctness where

    correctness : ¬ (φ ⇒ ψ) ⟺ nnfφ ∧ nnf¬ψ
    correctness ρ = begin
      ⟦ ¬ (φ ⇒ ψ) ⟧ ρ ≡⟨ semantics¬⇒𝔹 _ _ ⟩
      ⟦ φ ∧ ¬ ψ ⟧ ρ ≡⟨ cong2 _∧𝔹_ (φ⟺nnfφ ρ) (¬ψ⟺nnf¬ψ ρ) ⟩
      ⟦ nnfφ ∧ nnf¬ψ ⟧ ρ ∎

nnf¬ (φ ⇔ ψ) with nnf φ | nnf¬ φ | nnf ψ | nnf¬ ψ
... | nnfφ , NNFφ , φ⟺nnfφ
    | nnf¬φ , NNF¬φ , ¬φ⟺nnf¬φ
    | nnfψ , NNFψ , ψ⟺nnfψ
    | nnf¬ψ , NNF¬ψ , ¬ψ⟺nnf¬ψ = nnfφ ∧ nnf¬ψ ∨ nnf¬φ ∧ nnfψ , NNFφ ∧ NNF¬ψ ∨ NNF¬φ ∧ NNFψ , correctness where

    correctness : ¬ (φ ⇔ ψ) ⟺ nnfφ ∧ nnf¬ψ ∨ nnf¬φ ∧ nnfψ
    correctness ρ = begin
      ⟦ ¬ (φ ⇔ ψ) ⟧ ρ ≡⟨ semantics¬⇔𝔹 _ _ ⟩
      ⟦ φ ∧ ¬ ψ ∨ ¬ φ ∧ ψ ⟧ ρ ≡⟨ cong2 _∨𝔹_ (cong2 _∧𝔹_ (φ⟺nnfφ ρ) (¬ψ⟺nnf¬ψ ρ)) (cong2 _∧𝔹_ (¬φ⟺nnf¬φ ρ) (ψ⟺nnfψ ρ)) ⟩
      ⟦ nnfφ ∧ nnf¬ψ ∨ nnf¬φ ∧ nnfψ ⟧ ρ ∎
```


Example:

```
_ : dfst (nnf (¬ ¬ (` p₀ ⇒ ¬ (` p₁ ∧ ` p₂)))) ≡ ¬ ` p₀ ∨ ¬ ` p₁ ∨ ¬ ` p₂
_ = refl 
```

## Extended negation normal form {#ENNF}

Put here the one without blowup.

```
data ENNF : Formula → Set where
  ⊤ : ENNF ⊤
  ⊥ : ENNF ⊥
  `_ : (p : PropName) → ENNF (` p)
  ¬`_ : (p : PropName) → ENNF (¬ ` p)
  _∧_ : ∀ {φ ψ} → ENNF φ → ENNF ψ → ENNF (φ ∧ ψ)
  _∨_ : ∀ {φ ψ} → ENNF φ → ENNF ψ → ENNF (φ ∨ ψ)
  _⇒_ : ∀ {φ ψ} → ENNF φ → ENNF ψ → ENNF (φ ⇒ ψ)
  _⇔_ : ∀ {φ ψ} → ENNF φ → ENNF ψ → ENNF (φ ⇔ ψ)
```

Computation.

```
ennf : ∀ φ → ∃[ ψ ] ENNF ψ × φ ⟺ ψ
-- nnf¬ : ∀ {n} (φ : Formula n) → Σ (Formula n) λ ψ → NNF ψ × ¬ φ ⟺ ψ

ennf ⊤ = ⊤ , ⊤ , λ ρ → refl 
ennf ⊥ =  ⊥  , ⊥ , λ ρ → refl 
ennf (` x) = ` x , ` x , λ ρ → refl

ennf (φ ∧ ψ) with ennf φ | ennf ψ
... | ennfφ , ENNFφ , φ⟺ennfφ
    | ennfψ , ENNFψ , ψ⟺ennfψ = ennfφ ∧ ennfψ , ENNFφ ∧ ENNFψ , correctness where

    correctness : φ ∧ ψ ⟺ ennfφ ∧ ennfψ
    correctness ρ = cong2 _∧𝔹_ (φ⟺ennfφ ρ) (ψ⟺ennfψ ρ)

ennf (φ ∨ ψ) with ennf φ | ennf ψ
... | nnfφ , NNFφ , φ⟺nnfφ
    | nnfψ , NNFψ , ψ⟺nnfψ = nnfφ ∨ nnfψ , NNFφ ∨ NNFψ , correctness where

    correctness : φ ∨ ψ ⟺ nnfφ ∨ nnfψ
    correctness ρ = cong2 _∨𝔹_ (φ⟺nnfφ ρ) (ψ⟺nnfψ ρ)

ennf (φ ⇒ ψ) with ennf φ | ennf ψ
... | ennfφ , ENNFφ , φ⟺ennfφ
    | ennfψ , ENNFψ , ψ⟺ennfψ = ennfφ ⇒ ennfψ , ENNFφ ⇒ ENNFψ , correctness where

    correctness : φ ⇒ ψ ⟺ ennfφ ⇒ ennfψ
    correctness ρ = begin
      ⟦ φ ⇒ ψ ⟧ ρ ≡⟨ cong2 _⇒𝔹_ (φ⟺ennfφ ρ) (ψ⟺ennfψ ρ) ⟩
      ⟦ ennfφ ⇒ ennfψ ⟧ ρ ∎

ennf (φ ⇔ ψ) with ennf φ | ennf ψ
... | ennfφ , ENNFφ , φ⟺ennfφ
    | ennfψ , ENNFψ , ψ⟺ennfψ = ennfφ ⇔ ennfψ , ENNFφ ⇔ ENNFψ , correctness where

    correctness : φ ⇔ ψ ⟺ ennfφ ⇔ ennfψ
    correctness ρ = begin
      ⟦ φ ⇔ ψ ⟧ ρ ≡⟨ cong2 _⇔𝔹_ (φ⟺ennfφ ρ) (ψ⟺ennfψ ρ) ⟩
      ⟦ ennfφ ⇔ ennfψ ⟧ ρ ∎

ennf (¬ ⊤) =  ⊥ , ⊥ , λ ρ → refl
ennf (¬ ⊥) =  ⊤ , ⊤ , λ ρ → refl
ennf (¬ ` p) =  ¬ ` p , ¬` p , λ ρ → refl

ennf (¬ ¬ φ) with ennf φ
... | ennfφ , ENNFφ , φ⟺ennfφ = ennfφ , ENNFφ , correctness where

  correctness : ¬ ¬ φ ⟺ ennfφ
  correctness ρ = begin
    ⟦ ¬ ¬ φ ⟧ ρ ≡⟨ doubleNegationLaw φ ρ ⟩
    ⟦ φ ⟧ ρ ≡⟨ φ⟺ennfφ ρ ⟩
    ⟦ ennfφ ⟧ ρ ∎

ennf (¬ (φ ∧ ψ)) with ennf (¬ φ) | ennf (¬ ψ)
... | ennf¬φ , ENNF¬φ , ¬φ⟺ennf¬φ
    | ennf¬ψ , ENNF¬ψ , ¬ψ⟺ennf¬ψ = ennf¬φ ∨ ennf¬ψ , ENNF¬φ ∨ ENNF¬ψ , correctness where

    correctness : ¬ (φ ∧ ψ) ⟺ ennf¬φ ∨ ennf¬ψ
    correctness ρ = begin
      ⟦ ¬ (φ ∧ ψ) ⟧ ρ ≡⟨ deMorganAnd φ ψ ρ ⟩
      ⟦ ¬ φ ∨ ¬ ψ ⟧ ρ ≡⟨⟩
      ⟦ ¬ φ ⟧ ρ ∨𝔹 ⟦ ¬ ψ ⟧ ρ ≡⟨ cong2 _∨𝔹_ (¬φ⟺ennf¬φ ρ) (¬ψ⟺ennf¬ψ ρ) ⟩
      ⟦ ennf¬φ ⟧ ρ ∨𝔹 ⟦ ennf¬ψ ⟧ ρ ≡⟨⟩
      ⟦ ennf¬φ ∨ ennf¬ψ ⟧ ρ ∎

ennf (¬ (φ ∨ ψ)) with ennf (¬ φ) | ennf (¬ ψ)
... | ennf¬φ , ENNF¬φ , ¬φ⟺ennf¬φ
    | ennf¬ψ , ENNF¬ψ , ¬ψ⟺ennf¬ψ = ennf¬φ ∧ ennf¬ψ , ENNF¬φ ∧ ENNF¬ψ , correctness where

    correctness : ¬ (φ ∨ ψ) ⟺ ennf¬φ ∧ ennf¬ψ
    correctness ρ = begin
      ⟦ ¬ (φ ∨ ψ) ⟧ ρ ≡⟨ deMorganOr φ ψ ρ ⟩
      ⟦ ¬ φ ∧ ¬ ψ ⟧ ρ ≡⟨⟩
      ⟦ ¬ φ ⟧ ρ ∧𝔹 ⟦ ¬ ψ ⟧ ρ ≡⟨ cong2 _∧𝔹_ (¬φ⟺ennf¬φ ρ) (¬ψ⟺ennf¬ψ ρ) ⟩
      ⟦ ennf¬φ ⟧ ρ ∧𝔹 ⟦ ennf¬ψ ⟧ ρ ≡⟨⟩
      ⟦ ennf¬φ ∧ ennf¬ψ ⟧ ρ ∎

ennf (¬ (φ ⇒ ψ)) with ennf φ | ennf (¬ ψ)
... | ennfφ , ENNFφ , φ⟺ennfφ
    | ennf¬ψ , ENNF¬ψ , ¬ψ⟺ennf¬ψ = ennfφ ∧ ennf¬ψ , ENNFφ ∧ ENNF¬ψ , correctness where

    correctness : ¬ (φ ⇒ ψ) ⟺ ennfφ ∧ ennf¬ψ
    correctness ρ = begin
      ⟦ ¬ (φ ⇒ ψ) ⟧ ρ ≡⟨ semantics¬⇒𝔹 _ _ ⟩
      ⟦ φ ∧ ¬ ψ ⟧ ρ ≡⟨ cong2 _∧𝔹_ (φ⟺ennfφ ρ) (¬ψ⟺ennf¬ψ ρ) ⟩
      ⟦ ennfφ ∧ ennf¬ψ ⟧ ρ ∎

ennf (¬ (φ ⇔ ψ)) with ennf (¬ φ) | ennf ψ
... | ennf¬φ , ENNF¬φ , ¬φ⟺ennf¬φ
    | ennfψ , ENNFψ , ψ⟺ennfψ = ennf¬φ ⇔ ennfψ , ENNF¬φ ⇔ ENNFψ , correctness where

    correctness : ¬ (φ ⇔ ψ) ⟺ ennf¬φ ⇔ ennfψ
    correctness ρ = begin
      ⟦ ¬ (φ ⇔ ψ) ⟧ ρ ≡⟨ push¬⇔𝔹 _ _ ⟩
      ⟦ (¬ φ ⇔ ψ) ⟧ ρ ≡⟨ cong2 _⇔𝔹_ (¬φ⟺ennf¬φ ρ) (ψ⟺ennfψ ρ) ⟩
      ⟦ ennf¬φ ⇔ ennfψ ⟧ ρ ∎
```

Example:
```
_ : dfst (ennf (¬ ¬ (` p₀ ⇒ ¬ (` p₁ ∧ ` p₂)))) ≡ ` p₀ ⇒ ¬ ` p₁ ∨ ¬ ` p₂
_ = refl 
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



We show that the NNF formula produced by [`ennf`](#ennf) has size linear in the input.

```
ennf' : Formula → Formula
ennf' φ = dfst (ennf φ)

ennf-size  : ∀ φ → size (ennf' φ) ≤ 2 * size φ
```

In order to prove [`ennf-size`](#ennf-size) above,
it is useful to have the following stronger invariant for negated formulas.

```
ennf-size¬ : ∀ φ → size (ennf' (¬ φ)) ≤ 2 * size φ
```

We can now proceed to prove [`ennf-size`](#ennf-size) and [`ennf-size¬`](#ennf-size¬) by mutual induction.
The last four cases follow a similar pattern.
We first abstract the pattern and then apply it several times.

```
size-reasoning : (a b c d : ℕ) (_ : a ≤ 2 * c) (_ : b ≤ 2 * d) → 1 + a + b ≤ 2 * (1 + c + d)
```

```
ennf-size ⊤ = s≤s 0≤n
ennf-size ⊥ = s≤s 0≤n
ennf-size (` p) = s≤s 0≤n

ennf-size (¬ φ) with ennf-size¬ φ
... | ind¬φ = begin≤
  size (ennf' (¬ φ)) ≤⟨ ind¬φ ⟩
  2 * size φ ≤⟨ cong-≤ (Num 2 *C □) (size-¬ φ) ⟩
  2 * size (¬ φ) ∎≤

ennf-size (φ ∧ ψ) with ennf-size φ | ennf-size ψ
... | indφ | indψ = begin≤
  size (ennf' (φ ∧ ψ)) ≤⟨⟩
  size (ennf' φ ∧ ennf' ψ) ≤⟨⟩
  1 + size (ennf' φ) + size (ennf' ψ) ≤⟨ size-reasoning _ _ (size φ) _ indφ indψ ⟩
  2 * (1 + size φ + size ψ) ≤⟨⟩
  2 * size (φ ∧ ψ) ∎≤
```

The last three cases are similar and we give them in a shortened form.

```
ennf-size (φ ∨ ψ) = size-reasoning _ _ (size φ) _ (ennf-size φ) (ennf-size ψ)
ennf-size (φ ⇒ ψ) = size-reasoning _ _ (size φ) _ (ennf-size φ) (ennf-size ψ)
ennf-size (φ ⇔ ψ) = size-reasoning _ _ (size φ) _ (ennf-size φ) (ennf-size ψ)
```

Proof for negated formulas:
```
ennf-size¬ ⊤ = s≤s 0≤n
ennf-size¬ ⊥ = s≤s 0≤n
ennf-size¬ (` p) = s≤s (s≤s 0≤n)

-- double negation!
ennf-size¬ (¬ φ) with ennf-size φ
... | indφ = begin≤
  size (ennf' (¬ ¬ φ)) ≤⟨⟩
  size (ennf' φ) ≤⟨ indφ ⟩
  2 * size φ ≤⟨ cong-≤ (Num 2 *C □) (size-¬ φ) ⟩
  2 * size (¬ φ) ∎≤ 

ennf-size¬ (φ ∧ ψ) = size-reasoning _ _ (size φ) _ (ennf-size¬ φ) (ennf-size¬ ψ)
ennf-size¬ (φ ∨ ψ) = size-reasoning _ _ (size φ) _ (ennf-size¬ φ) (ennf-size¬ ψ)
ennf-size¬ (φ ⇒ ψ) = size-reasoning _ _ (size φ) _ (ennf-size φ) (ennf-size¬ ψ)
ennf-size¬ (φ ⇔ ψ) = size-reasoning _ _ (size φ) _ (ennf-size¬ φ) (ennf-size ψ)
```

We now prove the common workhorse...
```
size-reasoning a b c d a≤c b≤d = begin≤
  1 + a + b
    ≤≡⟨ assoc-+ {1} {a} ⟩
  1 + ( a + b)
    ≤⟨ {! cong2-≤ (Num 1 +C (□ fzero +C □ (fsuc fzero))) a≤c b≤d !} ⟩ --alternative: arithmetic expressions with variables
  1 + (2 * c + 2 * d)
    ≤≡⟨ cong (_+_ 1) (assocLeft-+* {2} {c}) ⟩
  1 + 2 * (c + d)
    ≤⟨ cong-≤ (□ +C Num _) 1≤2*1 ⟩
  2 * 1 + 2 * (c + d)
    ≤≡⟨ assocLeft-+* {2} {1} ⟩
  2 * (1 + c + d) ∎≤
```

The worst-case behaviour is achieved when a single negation is pushed down to the leaves
in a negation-free formula consisting of only [`∧`](#_∧_) and [`∨`](#_∨_)

## Disjunctive normal form {#DNF}

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

### Case 1: DNF of a disjunction

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

### Case 2: DNF of a conjunction

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

## Conjunctive normal form {#CNF}

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
