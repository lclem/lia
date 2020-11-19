---
title: "Gentzen's natural deduction 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas  #-}

open import part0.index

module part2.NaturalDeduction (n' : ℕ) where
```

# Syntax

The syntax of intuitionistic propositional logic is the same as its classical counterpart.
However, the semantics is different.

```
infix 100 `_
infix 99 ¬_
infixr 98 _∧_
infixr 97 _∨_ _⇒_
infixr 96 _⇔_

n = 3 + n'
PropName = Fin n

p₀ p₁ p₂ : PropName
p₀ = fzero
p₁ = fsuc fzero 
p₂ = fsuc (fsuc fzero)

data Formula : Set where
  ⊤ ⊥ : Formula
  `_ : (p : PropName) → Formula
  _∧_ _∨_ _⇒_ : (φ ψ : Formula) → Formula
```

The connectives `¬ φ` and `φ ⇔ ψ` are derived connectives
and they are just interpreted as abbreviations for
`φ ⇒ ⊥` and `(φ ⇒ ψ) ∧ (ψ ⇒ φ)`.

```
¬_ : Formula → Formula
¬ φ = φ ⇒ ⊥

_⇔_ : Formula → Formula → Formula
φ ⇔ ψ = (φ ⇒ ψ) ∧ (ψ ⇒ φ)
```

## Equality

```
instance
  eqFormula : Eq Formula
  _≡?_ {{eqFormula}} = go where

    go : ∀ φ ψ → Dec (φ ≡ ψ)
    go ⊤ ⊤ = yes refl
    go ⊤ ⊥ = no λ ()
    go ⊤ (` _) = no λ ()
    go ⊤ (_ ∧ _) = no λ ()
    go ⊤ (_ ∨ _) = no λ ()
    go ⊤ (_ ⇒ _) = no λ ()
    go ⊥ ⊤ = no λ ()
    go ⊥ ⊥ = yes refl
    go ⊥ (` _) = no λ ()
    go ⊥ (_ ∧ _) = no λ ()
    go ⊥ (_ ∨ _) = no λ ()
    go ⊥ (_ ⇒ _) = no λ ()
    go (` _) ⊤ = no λ ()
    go (` _) ⊥ = no λ ()
    go (` p) (` q) with p ≡? q
    ... | yes refl = yes refl
    ... | no p≢q = no λ{ refl → p≢q refl}
    go (` _) (_ ∧ _) = no λ ()
    go (` _) (_ ∨ _) = no λ ()
    go (` _) (_ ⇒ _) = no λ ()
    go (_ ∧ _) ⊤ = no λ ()
    go (_ ∧ _) ⊥ = no λ ()
    go (_ ∧ _) (` _) = no λ ()
    go (φ₁ ∧ ψ1) (φ2 ∧ ψ2) with go φ₁ φ2 ×? go ψ1 ψ2
    ... | yes (refl , refl) = yes refl
    ... | no neq = no λ{ refl → neq (refl , refl)}
    go (_ ∧ _) (_ ∨ _) = no λ ()
    go (_ ∧ _) (_ ⇒ _) = no λ ()
    go (_ ∨ _) ⊤ = no λ ()
    go (_ ∨ _) ⊥ = no λ ()
    go (_ ∨ _) (` _) = no λ ()
    go (_ ∨ _) (_ ∧ _) = no λ ()
    go (φ₁ ∨ ψ1) (φ2 ∨ ψ2) with go φ₁ φ2 ×? go ψ1 ψ2
    ... | yes (refl , refl) = yes refl
    ... | no neq = no λ{ refl → neq (refl , refl)}
    go (_ ∨ _) (_ ⇒ _) = no λ ()
    go (_ ⇒ _) ⊤ = no λ ()
    go (_ ⇒ _) ⊥ = no λ ()
    go (_ ⇒ _) (` _) = no λ ()
    go (_ ⇒ _) (_ ∧ _) = no λ ()
    go (_ ⇒ _) (_ ∨ _) = no λ ()
    go (φ₁ ⇒ ψ1) (φ2 ⇒ ψ2) with go φ₁ φ2 ×? go ψ1 ψ2
    ... | yes (refl , refl) = yes refl
    ... | no neq = no λ{ refl → neq (refl , refl)}
```

## Contexts

```
Context = Formula *

∅ : Context
∅ = ε

infixl 50 _·_  
_·_ : Context → Formula → Context
Γ · φ = φ ∷ Γ

private
  variable
    p q r : PropName
    φ ψ θ : Formula
    Γ Δ : Context
```

# Natural deduction proofs

```
infixr 5 _⊢_
data _⊢_ : Context → Formula → Set where

  A : φ ∈ Γ →
      -------
      Γ ⊢ φ

  ⊤I : ----------
       Γ ⊢ ⊤

  ⇒I : Γ · φ ⊢ ψ →
       ------------
       Γ ⊢ φ ⇒ ψ

  ⇒E : Γ ⊢ φ ⇒ ψ →
       Γ ⊢ φ →
       -----------
       Γ ⊢ ψ

  ∧I : Γ ⊢ φ →
       Γ ⊢ ψ →
       -----------
       Γ ⊢ φ ∧ ψ

  ∧E-left :
    Γ ⊢ φ ∧ ψ →
    -----------
    Γ ⊢ φ
  
  ∧E-right :
    Γ ⊢ φ ∧ ψ →
    -----------
    Γ ⊢ ψ

  ∨I-left :
    Γ ⊢ φ →
    -----------
    Γ ⊢ φ ∨ ψ

  ∨I-right :
    Γ ⊢ ψ →
    -----------
    Γ ⊢ φ ∨ ψ

  ∨E :
    Γ ⊢ φ ∨ ψ →
    Γ · φ ⊢ θ →
    Γ · ψ ⊢ θ →
    -----------
    Γ ⊢ θ

  ⊥E :
    Γ ⊢ ⊥ →
    ----------
    Γ ⊢ φ

Theorem : Formula → Set
Theorem φ = ∅ ⊢ φ
```

## Examples

```
E0 : ∀ φ → ∅ ⊢ φ ⇒ φ
E0 φ = ⇒I (A here)

E1 : ∀ φ → ∅ ⊢ φ ⇒ ¬ ¬ φ
E1 φ = ⇒I (⇒I Δ₀⊢⊥)  where

  Δ₀ : Context
  Δ₀ = ∅ · φ · (¬ φ)

  Δ₀⊢φ : Δ₀ ⊢ φ
  Δ₀⊢φ = A (there here)

  Δ₀⊢¬φ : Δ₀ ⊢ ¬ φ
  Δ₀⊢¬φ = A here

  Δ₀⊢⊥ : Δ₀ ⊢ ⊥
  Δ₀⊢⊥ = ⇒E Δ₀⊢¬φ Δ₀⊢φ

E2 : ∀ φ ψ → ∅ ⊢ ¬ (φ ∨ ψ) ⇒ ¬ φ ∧ ¬ ψ
E2 φ ψ = {!!}

E3 : ∀ φ ψ → ∅ ⊢ ¬ φ ∧ ¬ ψ ⇒ ¬ (φ ∨ ψ)
E3 φ ψ = {!!}

E4 : ∀ φ ψ → ∅ ⊢ ¬ φ ∨ ¬ ψ ⇒ ¬ (φ ∧ ψ)
E4 φ ψ = {!!}
```

More examples...

```
G1 : ∀ φ → ∅ ⊢ ¬ ¬ (φ ∨ ¬ φ)
G1 φ = step8 where

  Δ₀ = ∅ · (¬ (φ ∨ ¬ φ)) · φ

  step0 : Δ₀ ⊢ φ
  step0 = A here

  step1 : Δ₀ ⊢ φ ∨ ¬ φ
  step1 = ∨I-left step0

  step2 : Δ₀ ⊢ ¬ (φ ∨ ¬ φ)
  step2 = A (there here)

  step3 : Δ₀ ⊢ ⊥
  step3 = ⇒E step2 step1

  Δ₁ = ∅ · ¬ (φ ∨ ¬ φ)

  step4 : Δ₁ ⊢ ¬ φ
  step4 = ⇒I step3

  step5 : Δ₁ ⊢ φ ∨ ¬ φ
  step5 = ∨I-right step4

  step6 : Δ₁ ⊢ ¬ (φ ∨ ¬ φ)
  step6 = A here

  step7 : Δ₁ ⊢ ⊥
  step7 = ⇒E step6 step5

  step8 : ∅ ⊢ ¬ ¬ (φ ∨ ¬ φ)
  step8 = ⇒I step7

G2 : ∀ φ → [ (¬ ¬ ¬ φ) ] ⊢ ¬ φ
G2 φ = step6 where

  Δ₀ = ∅ · (¬ ¬ ¬ φ) · φ · (¬ φ)

  step0 : Δ₀ ⊢ φ
  step0 = A (there here)

  step1 : Δ₀ ⊢ ¬ φ
  step1 = A here

  step2 : Δ₀ ⊢ ⊥
  step2 = ⇒E step1 step0

  Δ₁ = ∅ · (¬ ¬ ¬ φ) · φ
  
  step3 : Δ₁ ⊢ ¬ ¬ φ
  step3 = ⇒I step2

  step4 : Δ₁ ⊢ ¬ ¬ ¬ φ
  step4 = A (there here)

  step5 : Δ₁ ⊢ ⊥
  step5 = ⇒E step4 step3

  step6 : ∅ · (¬ ¬ ¬ φ) ⊢ ¬ φ
  step6 = ⇒I step5
```

## Monotonicity

```
mon-⊢ weakening : Δ ⊢ φ → Δ ⊆ Γ → Γ ⊢ φ
mon-⊢ {φ} {Δ} {Γ} = {!!}

weakening = mon-⊢
```

## Consistency

```
consistent : ~ (∅ ⊢ ⊥)
consistent = {!!}
```

## Deduction theorem

```
deductionTheorem : Γ · φ ⊢ ψ → Γ ⊢ φ ⇒ ψ
deductionTheorem = {! !}
```

## Double-negation proofs

```
infix 90 ¬¬_
¬¬_ : Context → Context
¬¬_ = map (¬_ ∘ ¬_)

DNP : ∀ Γ φ → Γ ⊢ φ → ¬¬ Γ ⊢ ¬ ¬ φ

DNP Γ φ (A φ∈Γ) = {! !}

DNP Γ ⊤ ⊤I = {! !}

-- Δ , ¬ ¬ φ ⊢ ¬ ¬ ψ IMPLIES Δ ⊢ ¬ ¬ (φ ⇒ ψ)
DNP Γ (φ ⇒ ψ) (⇒I Γ,φ⊢ψ)
  with DNP (Γ · φ) ψ Γ,φ⊢ψ
... | ¬¬Γ,¬¬φ⊢¬¬ψ = {! ⇒I ¬¬Γ,¬¬φ⊢¬¬ψ !}

-- Δ ⊢ ¬ ¬ ψ AND Δ ⊢ ¬ ¬ (ψ ⇒ φ) IMPLIES Δ ⊢ ¬ ¬ φ
DNP Γ φ (⇒E {φ = ψ} {ψ = φ} Γ⊢ψ⇒φ Γ⊢ψ)
  with DNP Γ (ψ ⇒ φ) Γ⊢ψ⇒φ |
       DNP Γ ψ Γ⊢ψ
... | ind1 | ind2 = {!!}

-- Δ ⊢ ¬ ¬ φ AND Δ ⊢ ¬ ¬ ψ IMPLIES Δ ⊢ ¬ ¬ (φ ∧ ψ)
DNP Γ (φ ∧ ψ) (∧I Γ⊢φ Γ⊢ψ)
  with DNP Γ φ Γ⊢φ |
       DNP Γ ψ Γ⊢ψ
... | ind1 | ind2 = {!!}

-- Δ ⊢ ¬ ¬ (φ ∧ ψ) IMPLIES Δ ⊢ ¬ ¬ φ
DNP Γ φ (∧E-left {ψ = ψ} Γ⊢φ∧ψ)
  with DNP Γ (φ ∧ ψ) Γ⊢φ∧ψ
... | ind = {!!}

-- Δ ⊢ ¬ ¬ (φ ∧ ψ) IMPLIES Δ ⊢ ¬ ¬ ψ
DNP Γ φ (∧E-right Γ⊢ψ∧φ)
  with DNP Γ _ Γ⊢ψ∧φ
... | ind = {!!}

--  Δ ⊢ ¬ ¬ φ IMPLIES Δ ⊢ ¬ ¬ (φ ∨ ψ)
DNP Γ (φ ∨ ψ) (∨I-left Γ⊢φ)
  with DNP Γ φ Γ⊢φ
... | ind = {!!}

-- Δ ⊢ ¬ ¬ ψ IMPLIES Δ ⊢ ¬ ¬ (φ ∨ ψ)
DNP Γ (φ ∨ ψ) (∨I-right Γ⊢ψ)
  with DNP Γ ψ Γ⊢ψ
... | ind = {!!}

-- Δ ⊢ ¬ ¬ (ψ ∨ ξ) AND Δ , ¬ ¬ ψ ⊢ ¬ ¬ φ AND Δ , ¬ ¬ ξ ⊢ ¬ ¬ φ IMPLIES Δ ⊢ ¬ ¬ φ
DNP Γ φ (∨E {ψ} {ξ} Γ⊢ψ∨ξ Γ,ψ⊢φ Γ,ξ⊢φ)
  with DNP _ _ Γ⊢ψ∨ξ |
       DNP _ _ Γ,ψ⊢φ |
       DNP _ _ Γ,ξ⊢φ
... | ind1 | ind2 | ind3 = {!!}

-- Δ ⊢ ¬ ¬ ⊥ IMPLIES Δ ⊢ ¬ ¬ φ
DNP Γ φ (⊥E Γ⊢⊥)
  with DNP _ _ Γ⊢⊥
... | ind = {!!}
```
