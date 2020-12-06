---
title: "Gentzen's natural deduction 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas  #-}

open import part0.index

module part1.NaturalDeduction (n' : ℕ) where
open import part1.Hilbert n' public renaming (_⊢_ to _⊢H_; soundness to soundness-H; completeness to completeness-H)

private
  variable
    p q r : PropName
    φ ψ θ ξ : Formula
    Γ Δ Ψ Ξ : Context
```

# Natural deduction

```
infixr 5 _⊢_
infix 12 Ass_
data _⊢_ : Context → Formula → Set where

  Ass_ : φ ∈ Γ →
         -------
         Γ ⊢ φ

  ⊤I : -----
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

  -- double negation eliminatiion
  ⊥⊥E :
    Γ ⊢ (φ ⇒ ⊥) ⇒ ⊥ →
    -----
    Γ ⊢ φ

  -- derived connectives

  ¬I :
    Γ ⊢ φ ⇒ ⊥ →
    ----------
    Γ ⊢ ¬ φ

  ¬E :
    Γ ⊢ ¬ φ →
    ----------
    Γ ⊢ φ ⇒ ⊥

  ⇔I :
    Γ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ) →
    ---------------------
    Γ ⊢ φ ⇔ ψ

  ⇔E :
    Γ ⊢ φ ⇔ ψ →
    ---------------------
    Γ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)

Theorem : Formula → Set
Theorem φ = ∅ ⊢ φ
```

## Weakening

```
weakening-ND :
  Δ ⊢ φ →
  Δ ⊆ Γ →
  -----
  Γ ⊢ φ

weakening-ND (Ass φ∈Δ) Δ⊆Γ = Ass Δ⊆Γ φ∈Δ

weakening-ND ⊤I Δ⊆Γ = ⊤I

weakening-ND {Δ} {φ ⇒ ψ} {Γ} (⇒I Δ·φ⊢ψ) Δ⊆Γ = ⇒I (weakening-ND Δ·φ⊢ψ (⊆-cons-1 Δ⊆Γ))

weakening-ND (⇒E Δ⊢φ⇒ψ Δ⊢φ) Δ⊆Γ = ⇒E (weakening-ND Δ⊢φ⇒ψ Δ⊆Γ) (weakening-ND Δ⊢φ Δ⊆Γ)

weakening-ND (∧I Δ⊢φ Δ⊢ψ) Δ⊆Γ = ∧I (weakening-ND Δ⊢φ Δ⊆Γ) (weakening-ND Δ⊢ψ Δ⊆Γ)

weakening-ND (∧E-left Δ⊢φ) Δ⊆Γ = ∧E-left (weakening-ND Δ⊢φ Δ⊆Γ)

weakening-ND (∧E-right Δ⊢φ) Δ⊆Γ = ∧E-right (weakening-ND Δ⊢φ Δ⊆Γ)

weakening-ND (∨I-left Δ⊢φ) Δ⊆Γ = ∨I-left (weakening-ND Δ⊢φ Δ⊆Γ)

weakening-ND (∨I-right Δ⊢φ) Δ⊆Γ = ∨I-right (weakening-ND Δ⊢φ Δ⊆Γ)

weakening-ND {Δ} {θ} {Γ} (∨E {Δ} {φ} {ψ} {θ} Δ⊢φ∨ψ Δ·φ⊢θ Δ·ψ⊢θ) Δ⊆Γ
  with weakening-ND Δ⊢φ∨ψ Δ⊆Γ |
       weakening-ND Δ·φ⊢θ (⊆-cons-1 Δ⊆Γ) |
       weakening-ND Δ·ψ⊢θ (⊆-cons-1 Δ⊆Γ)
... | Γ⊢φ∨ψ | Γ·φ⊢θ | Γ·ψ⊢θ = ∨E Γ⊢φ∨ψ Γ·φ⊢θ Γ·ψ⊢θ

weakening-ND (⊥E Δ⊢φ) Δ⊆Γ = ⊥E (weakening-ND Δ⊢φ Δ⊆Γ)

weakening-ND (⊥⊥E Δ⊢φ) Δ⊆Γ = ⊥⊥E (weakening-ND Δ⊢φ Δ⊆Γ)

weakening-ND (¬I Δ⊢φ⇒⊥) Δ⊆Γ
  with weakening-ND Δ⊢φ⇒⊥ Δ⊆Γ
... | Γ⊢φ⇒⊥ = ¬I Γ⊢φ⇒⊥

weakening-ND (¬E Δ⊢¬φ) Δ⊆Γ
  with weakening-ND Δ⊢¬φ Δ⊆Γ
... | Γ⊢¬φ = ¬E Γ⊢¬φ

weakening-ND (⇔I Δ⊢φ) Δ⊆Γ = ⇔I (weakening-ND Δ⊢φ Δ⊆Γ)

weakening-ND (⇔E Δ⊢φ) Δ⊆Γ = ⇔E (weakening-ND Δ⊢φ Δ⊆Γ)
```

## Deduction theorem

Now one direction is totally obvious, since it is built into the system:

```
DT2-ND :
  Γ · φ ⊢ ψ →
  ----------
  Γ ⊢ φ ⇒ ψ
DT2-ND = ⇒I
```

```
DT1-ND :
  Γ ⊢ φ ⇒ ψ →
  -----------
  Γ · φ ⊢ ψ

DT1-ND {Γ} {φ} {ψ} Γ⊢φ⇒ψ =
  BEGIN
  have Γ · φ ⊢ φ      by Ass here
  have Γ · φ ⊢ φ ⇒ ψ  by (weakening-ND Γ⊢φ⇒ψ there)
  have Γ · φ ⊢ ψ      apply ⇒E at here , back 1
  END
```

## Examples

```
-- S0 : ∀ φ → ∅ ⊢ φ ⇒ φ
-- S0 φ = ⇒I (Ass here)

-- S1 : ∀ φ → ∅ ⊢ φ ⇒ ¬ ¬ φ
-- S1 φ = {! ⇒I (⇒I Δ₀⊢⊥) !} where

--   Δ₀ : Context
--   Δ₀ = ∅ · φ · (¬ φ)

--   Δ₀⊢φ : Δ₀ ⊢ φ
--   Δ₀⊢φ = Ass (there here)

--   Δ₀⊢¬φ : Δ₀ ⊢ ¬ φ
--   Δ₀⊢¬φ = Ass here

--   Δ₀⊢⊥ : Δ₀ ⊢ ⊥
--   Δ₀⊢⊥ = {! ⇒E Δ₀⊢¬φ Δ₀⊢φ !}

-- S2 : ∀ φ ψ → ∅ ⊢ ¬ (φ ∨ ψ) ⇒ ¬ φ ∧ ¬ ψ
-- S2 φ ψ = {!!}

-- S3 : ∀ φ ψ → ∅ ⊢ ¬ φ ∧ ¬ ψ ⇒ ¬ (φ ∨ ψ)
-- S3 φ ψ = {!!}

-- S4 : ∀ φ ψ → ∅ ⊢ ¬ φ ∨ ¬ ψ ⇒ ¬ (φ ∧ ψ)
-- S4 φ ψ = {!!}
```

More examples...

```
-- G1 : ∀ φ → ∅ ⊢ ¬ ¬ (φ ∨ ¬ φ)
-- G1 φ = step8 where

--   Δ₀ = ∅ · (¬ (φ ∨ ¬ φ)) · φ

--   step0 : Δ₀ ⊢ φ
--   step0 = Asshere

--   step1 : Δ₀ ⊢ φ ∨ ¬ φ
--   step1 = ∨I-left step0

--   step2 : Δ₀ ⊢ ¬ (φ ∨ ¬ φ)
--   step2 = Ass(there here)

--   step3 : Δ₀ ⊢ ⊥
--   step3 = {! ⇒E step2 step1 !}

--   Δ₁ = ∅ · ¬ (φ ∨ ¬ φ)

--   step4 : Δ₁ ⊢ ¬ φ
--   step4 = ⇒I step3

--   step5 : Δ₁ ⊢ φ ∨ ¬ φ
--   step5 = ∨I-right step4

--   step6 : Δ₁ ⊢ ¬ (φ ∨ ¬ φ)
--   step6 = Asshere

--   step7 : Δ₁ ⊢ ⊥
--   step7 = ⇒E step6 step5

--   step8 : ∅ ⊢ ¬ ¬ (φ ∨ ¬ φ)
--   step8 = ⇒I step7

-- G2 : ∀ φ → [ (¬ ¬ ¬ φ) ] ⊢ ¬ φ
-- G2 φ = step6 where

--   Δ₀ = ∅ · (¬ ¬ ¬ φ) · φ · (¬ φ)

--   step0 : Δ₀ ⊢ φ
--   step0 = Ass(there here)

--   step1 : Δ₀ ⊢ ¬ φ
--   step1 = Asshere

--   step2 : Δ₀ ⊢ ⊥
--   step2 = ⇒E step1 step0

--   Δ₁ = ∅ · (¬ ¬ ¬ φ) · φ
  
--   step3 : Δ₁ ⊢ ¬ ¬ φ
--   step3 = ⇒I step2

--   step4 : Δ₁ ⊢ ¬ ¬ ¬ φ
--   step4 = Ass(there here)

--   step5 : Δ₁ ⊢ ⊥
--   step5 = ⇒E step4 step3

--   step6 : ∅ · (¬ ¬ ¬ φ) ⊢ ¬ φ
--   step6 = ⇒I step5
```

Useful examples:

```
A1-ND : Γ ⊢ φ ⇒ ψ ⇒ φ
A1-ND {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ · ψ ⊢ φ  by Ass back 1
  have Γ ⊢ φ ⇒ ψ ⇒ φ  apply ⇒I ∘ ⇒I at here 
  END
```

```
A2-ND : Γ ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ ξ
A2-ND {Γ} {φ} {ψ} {ξ} =
  BEGIN
  have Γ · φ ⇒ ψ ⇒ ξ · φ ⇒ ψ · φ ⊢ φ ⇒ ψ      by Ass back 1
  have Γ · φ ⇒ ψ ⇒ ξ · φ ⇒ ψ · φ ⊢ φ          by Ass here
  have Γ · φ ⇒ ψ ⇒ ξ · φ ⇒ ψ · φ ⊢ ψ          apply ⇒E at back 1 , here
  
  have Γ · φ ⇒ ψ ⇒ ξ · φ ⇒ ψ · φ ⊢ φ ⇒ ψ ⇒ ξ  by Ass back 2
  have Γ · φ ⇒ ψ ⇒ ξ · φ ⇒ ψ · φ ⊢ ψ ⇒ ξ      apply ⇒E at here , back 2
  have Γ · φ ⇒ ψ ⇒ ξ · φ ⇒ ψ · φ ⊢ ξ          apply ⇒E at here , back 2

  have Γ ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ ξ      apply ⇒I ∘ ⇒I ∘ ⇒I at here
  END
```

```
A3-ND : Γ ⊢ ((φ ⇒ ⊥) ⇒ ⊥) ⇒ φ
A3-ND {Γ} {φ} =
  BEGIN
  have Γ · (φ ⇒ ⊥) ⇒ ⊥ ⊢ (φ ⇒ ⊥) ⇒ ⊥  by Ass here
  have Γ · (φ ⇒ ⊥) ⇒ ⊥ ⊢ φ            apply ⊥⊥E at here
  have Γ ⊢ ((φ ⇒ ⊥) ⇒ ⊥) ⇒ φ          apply ⇒I at here
  END
```

```
N1-ND : Γ ⊢ ¬ φ ⇒ φ ⇒ ⊥
N1-ND {Γ} {φ} =
  BEGIN
  have Γ · ¬ φ · φ ⊢ ¬ φ    by Ass back 1
  have Γ · ¬ φ · φ ⊢ φ ⇒ ⊥  apply ¬E at here
  have Γ · ¬ φ · φ ⊢ φ      by Ass here
  have Γ · ¬ φ · φ ⊢ ⊥      apply ⇒E at back 1 , here
  have Γ ⊢ ¬ φ ⇒ φ ⇒ ⊥      apply ⇒I ∘ ⇒I at here
  END
```

```
N2-ND : Γ ⊢ (φ ⇒ ⊥) ⇒ ¬ φ
N2-ND {Γ} {φ} =
  BEGIN
  have Γ · φ ⇒ ⊥ ⊢ φ ⇒ ⊥      by Ass here
  have Γ · φ ⇒ ⊥ ⊢ ¬ φ        apply ¬I at here
  have Γ ⊢ (φ ⇒ ⊥) ⇒ ¬ φ      apply ⇒I at here
  END
```


```
D1-ND : Γ ⊢ φ ⇒ φ ∨ ψ
D1-ND {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ⊢ φ        by Ass here
  have Γ · φ ⊢ φ ∨ ψ    apply ∨I-left at here
  have Γ ⊢ φ ⇒ φ ∨ ψ    apply ⇒I at here
  END
```

```
D2-ND : Γ ⊢ ψ ⇒ φ ∨ ψ
D2-ND {Γ} {ψ} {φ} =
  BEGIN
  have Γ · ψ ⊢ ψ        by Ass here
  have Γ · ψ ⊢ φ ∨ ψ    apply ∨I-right at here
  have Γ ⊢ ψ ⇒ φ ∨ ψ    apply ⇒I at here
  END
```

```
D3-ND : Γ ⊢ (φ ⇒ θ) ⇒ (ψ ⇒ θ) ⇒ (φ ∨ ψ) ⇒ θ
D3-ND {Γ} {φ} {θ} {ψ} =
  BEGIN
  have Γ · φ ⇒ θ · ψ ⇒ θ · φ ∨ ψ ⊢ φ ⇒ θ      by Ass back 2
  have Γ · φ ⇒ θ · ψ ⇒ θ · φ ∨ ψ · φ ⊢ θ      apply DT1-ND at here

  have Γ · φ ⇒ θ · ψ ⇒ θ · φ ∨ ψ ⊢ ψ ⇒ θ      by Ass back 1
  have Γ · φ ⇒ θ · ψ ⇒ θ · φ ∨ ψ · ψ ⊢ θ      apply DT1-ND at here

  have Γ · φ ⇒ θ · ψ ⇒ θ · φ ∨ ψ ⊢ φ ∨ ψ      by Ass here
  have Γ · φ ⇒ θ · ψ ⇒ θ · φ ∨ ψ ⊢ θ          apply ∨E at here , back 3 , back 1
  have Γ ⊢ (φ ⇒ θ) ⇒ (ψ ⇒ θ) ⇒ (φ ∨ ψ) ⇒ θ    apply ⇒I ∘ ⇒I ∘ ⇒I at here
  END
```

```
C1-ND : Γ ⊢ φ ∧ ψ ⇒ φ
C1-ND {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ∧ ψ ⊢ φ ∧ ψ      by Ass here
  have Γ · φ ∧ ψ ⊢ φ          apply ∧E-left at here
  have Γ ⊢ φ ∧ ψ ⇒ φ          apply ⇒I at here
  END
```

```
C2-ND : Γ ⊢ φ ∧ ψ ⇒ ψ
C2-ND {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ∧ ψ ⊢ φ ∧ ψ      by Ass here
  have Γ · φ ∧ ψ ⊢ ψ          apply ∧E-right at here
  have Γ ⊢ φ ∧ ψ ⇒ ψ          apply ⇒I at here
  END
```

```
C3-ND : Γ ⊢ φ ⇒ ψ ⇒ φ ∧ ψ
C3-ND {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ · ψ ⊢ φ        by Ass back 1
  have Γ · φ · ψ ⊢ ψ        by Ass here
  have Γ · φ · ψ ⊢ φ ∧ ψ    apply ∧I at back 1 , here
  have Γ ⊢ φ ⇒ ψ ⇒ φ ∧ ψ    apply ⇒I ∘ ⇒I at here
  END
```

```
E1-ND : Γ ⊢ (φ ⇔ ψ) ⇒ φ ⇒ ψ
E1-ND {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ⇔ ψ · φ ⊢ φ ⇔ ψ              by Ass back 1
  have Γ · φ ⇔ ψ · φ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)  apply ⇔E at here
  have Γ · φ ⇔ ψ · φ ⊢ φ ⇒ ψ              apply ∧E-left at here
  have Γ · φ ⇔ ψ · φ ⊢ φ                  by Ass here
  have Γ · φ ⇔ ψ · φ ⊢ ψ                  apply ⇒E at back 1 , here
  have Γ ⊢ (φ ⇔ ψ) ⇒ φ ⇒ ψ                apply ⇒I ∘ ⇒I at here
  END
```

```
E2-ND : Γ ⊢ (φ ⇔ ψ) ⇒ ψ ⇒ φ
E2-ND {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ⇔ ψ · ψ ⊢ φ ⇔ ψ              by Ass back 1
  have Γ · φ ⇔ ψ · ψ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)  apply ⇔E at here
  have Γ · φ ⇔ ψ · ψ ⊢ ψ ⇒ φ              apply ∧E-right at here
  have Γ · φ ⇔ ψ · ψ ⊢ ψ                  by Ass here
  have Γ · φ ⇔ ψ · ψ ⊢ φ                  apply ⇒E at back 1 , here
  have Γ ⊢ (φ ⇔ ψ) ⇒ ψ ⇒ φ                apply ⇒I ∘ ⇒I at here
  END
```

```
E3-ND : Γ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ (φ ⇔ ψ)
E3-ND {Γ} {φ} {ψ} =
  BEGIN
  have Γ · φ ⇒ ψ · ψ ⇒ φ ⊢ φ ⇒ ψ              by Ass back 1
  have Γ · φ ⇒ ψ · ψ ⇒ φ ⊢ ψ ⇒ φ              by Ass here
  have Γ · φ ⇒ ψ · ψ ⇒ φ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)  apply ∧I at back 1 , here
  have Γ · φ ⇒ ψ · ψ ⇒ φ ⊢ φ ⇔ ψ              apply ⇔I at here
  have Γ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ (φ ⇔ ψ)        apply ⇒I ∘ ⇒I at here
  END
```

# Soundness and completeness

We show that the rules for natural deduction are sound and complete viAssmutual simulation of Hilbert-style proof system,
and leveraging on the fact that the latter is sound and complete.

For clarity:

```
_⊢ND_ = _⊢_
```

For the soundness property , it suffices to show that natural deduction can be simulated by Hilbert-style proofs:

```
ND→hilbert :
  Γ ⊢ND φ →
  ---------
  Γ ⊢H φ

ND→hilbert {Γ} {φ} (Ass φ∈Γ) = Ass φ∈Γ

ND→hilbert {Γ} {⊤} ⊤I = T1

ND→hilbert {Γ} {φ ⇒ ψ} (⇒I Γ⊢NDφ) = DT2 (ND→hilbert Γ⊢NDφ)

ND→hilbert {Γ} {φ} (⇒E {Γ} {ψ} Γ⊢NDφ⇒ψ Γ⊢NDψ)
  with ND→hilbert Γ⊢NDφ⇒ψ | ND→hilbert Γ⊢NDψ
... | Γ⊢Hφ⇒ψ | Γ⊢Hψ = MP Γ⊢Hφ⇒ψ Γ⊢Hψ

ND→hilbert {Γ} {φ ∧ ψ} (∧I Γ⊢NDφ Γ⊢NDψ)
  with ND→hilbert Γ⊢NDφ | ND→hilbert Γ⊢NDψ
... | Γ⊢Hφ | Γ⊢Hψ = MP2 C3 Γ⊢Hφ Γ⊢Hψ

ND→hilbert {Γ} {φ} (∧E-left {ψ = ψ} Γ⊢NDφ∧ψ)
  with ND→hilbert Γ⊢NDφ∧ψ
... | Γ⊢Hφ∧ψ = MP C1 Γ⊢Hφ∧ψ

ND→hilbert {Γ} {φ} (∧E-right {ψ = ψ} Γ⊢NDφ∧ψ)
  with ND→hilbert Γ⊢NDφ∧ψ
... | Γ⊢Hφ∧ψ = MP C2 Γ⊢Hφ∧ψ

ND→hilbert {Γ} {φ ∨ ψ} (∨I-left Γ⊢NDφ)
  with ND→hilbert Γ⊢NDφ
... | Γ⊢Hφ = MP D1 Γ⊢Hφ

ND→hilbert {Γ} {φ ∨ ψ} (∨I-right Γ⊢NDφ)
  with ND→hilbert Γ⊢NDφ
... | Γ⊢Hφ = MP D2 Γ⊢Hφ

ND→hilbert {Γ} {φ} (∨E {Γ} {ψ} {θ} Γ⊢NDψ∨θ Γ·ψ⊢NDφ Γ·θ⊢NDφ)
  with ND→hilbert Γ⊢NDψ∨θ | ND→hilbert Γ·ψ⊢NDφ | ND→hilbert Γ·θ⊢NDφ
... | Γ⊢Hψ∨θ | Γ·ψ⊢Hφ | Γ·θ⊢Hφ = MP3 D3 (DT2 Γ·ψ⊢Hφ) (DT2 Γ·θ⊢Hφ) Γ⊢Hψ∨θ

ND→hilbert {Γ} {φ} (⊥E Γ⊢ND⊥)
  with ND→hilbert Γ⊢ND⊥
... | Γ⊢H⊥ = MP B1 Γ⊢H⊥

ND→hilbert {Γ} {φ} (⊥⊥E Γ⊢ND[φ⇒⊥]⇒⊥)
  with ND→hilbert Γ⊢ND[φ⇒⊥]⇒⊥
... | Γ⊢H[φ⇒⊥]⇒⊥ = MP A3 Γ⊢H[φ⇒⊥]⇒⊥

ND→hilbert {Γ} {¬ φ} (¬I Γ⊢NDφ⇒⊥)
  with ND→hilbert Γ⊢NDφ⇒⊥
... | Γ⊢Hφ⇒⊥ = MP N2 Γ⊢Hφ⇒⊥

ND→hilbert {Γ} {φ ⇒ ⊥} (¬E Γ⊢ND¬φ)
  with ND→hilbert Γ⊢ND¬φ
... | Γ⊢H¬φ = MP N1 Γ⊢H¬φ

ND→hilbert {Γ} {φ ⇔ ψ} (⇔I Γ⊢ND[φ⇒ψ]∧[ψ⇒φ])
  with ND→hilbert Γ⊢ND[φ⇒ψ]∧[ψ⇒φ]
... | Γ⊢H[φ⇒ψ]∧[ψ⇒φ] = help2 (MP C1 Γ⊢H[φ⇒ψ]∧[ψ⇒φ]) (MP C2 Γ⊢H[φ⇒ψ]∧[ψ⇒φ])

ND→hilbert {Γ} {(φ ⇒ ψ) ∧ (ψ ⇒ φ)} (⇔E Γ⊢NDφ⇔ψ)
  with ND→hilbert Γ⊢NDφ⇔ψ
... | Γ⊢Hφ⇔ψ = MP2 C3 (help0 Γ⊢Hφ⇔ψ) (help1 Γ⊢Hφ⇔ψ)
```

```
soundness-ND : 
  Γ ⊢ND φ →
  -----
  Γ ⊨ φ

soundness-ND Γ⊢NDφ = soundness-H (ND→hilbert Γ⊢NDφ)
```

Notice how:

* Rule !ref(_⊢_)(⇒I) in natural deduction corresponds to the deduction theorem in Hilbert-style proofs.
* Rule !ref(_⊢_)(⇒E) in natural deduction corresponds to modus ponens in Hilbert-style proofs.

For the completeness property,
it suffices to show that Hilbert-style proofs can be simulated by natural deduction:

```
hilbert→ND :
  Γ ⊢H φ →
  -------
  Γ ⊢ND φ

hilbert→ND (Ass φ∈Γ) = Ass φ∈Γ
hilbert→ND A1 = A1-ND
hilbert→ND A2 = A2-ND
hilbert→ND A3 = A3-ND
hilbert→ND T1 = ⊤I
hilbert→ND N1 = N1-ND
hilbert→ND N2 = N2-ND
hilbert→ND D1 = D1-ND
hilbert→ND D2 = D2-ND
hilbert→ND D3 = D3-ND
hilbert→ND C1 = C1-ND
hilbert→ND C2 = C2-ND
hilbert→ND C3 = C3-ND
hilbert→ND E1 = E1-ND
hilbert→ND E2 = E2-ND
hilbert→ND E3 = E3-ND
hilbert→ND {Γ} {ψ} (MP {Γ} {φ} Γ⊢Hφ⇒ψ Γ⊢Hφ)
  with hilbert→ND Γ⊢Hφ⇒ψ | hilbert→ND Γ⊢Hφ
... | Γ⊢NDφ⇒ψ | Γ⊢NDφ = ⇒E Γ⊢NDφ⇒ψ Γ⊢NDφ
```

The application of modus ponens is simulated by the `⇒`-elimination rule !ref(_⊢_)(⇒E).

We obtain completeness for natural deduction thanks to completness of the Hilbert-style proof system and the fact that natural deduction simulates it:

```
completeness-ND : 
  Γ ⊨ φ →
  -----
  Γ ⊢ND φ

completeness-ND Γ⊨φ = hilbert→ND (completeness-H Γ⊨φ)
```

Invariance under context permutation.

```
perm-ND-left : Perm Γ Δ →
          Γ ⊢ φ →
          ----------------
          Δ ⊢ φ

perm-ND-left = {!   !}
```

Commutativity of disjunctions in the goal.
We use a semantic proof via completeness.

```
perm-ND-right : Perm Δ Ξ →
                Γ ⊢ ⋁ Δ →
                ----------
                Γ ⊢ ⋁ Ξ

-- does not seem to go through by induction on permutations
-- (classical logic does not satisfy the disjunction property)
-- perm-ND-right {ε} {Ξ} π Γ⊢⋁Δ = ⊥E Γ⊢⋁Δ
-- perm-ND-right {φ ∷ ε} {Ξ} π Γ⊢⋁Δ rewrite perm-singleton π = Γ⊢⋁Δ
-- perm-ND-right {φ ∷ Δ@(_ ∷ _)} {φ ∷ _ ∷ _} stop Γ⊢⋁Δ = Γ⊢⋁Δ
-- perm-ND-right {φ ∷ Δ@(ψ ∷ Δ′)} {φ ∷ Ξ} (skip π) Γ⊢⋁φ∷Δ
--   with perm-ND-right π {!   !} -- Γ⊢⋁Δ
-- ... | Γ⊢⋁Ξ = {!   !}
-- perm-ND-right {φ ∷ Δ@(_ ∷ _)} {.(_ ∷ φ ∷ _)} (swap π) Γ⊢⋁Δ = {!   !}
-- perm-ND-right {φ ∷ Δ@(_ ∷ _)} {Ξ} (tran π π₁) Γ⊢⋁Δ = {!   !}
perm-ND-right {Δ} {Ξ} {Γ} π Γ⊢⋁Δ =
  BEGIN
  have Γ ⊨ ⋁ Δ        by soundness-ND Γ⊢⋁Δ
  have ⋁ Δ ⟺ ⋁ Ξ    by permOr π
  have Γ ⊨ ⋁ Ξ        apply semantics-⟺ {Γ} {⋁ Δ} {⋁ Ξ} at back 1 , here
  have Γ ⊢ ⋁ Ξ        apply completeness-ND at here
  END
```

```
contraction-ND-left : Γ · φ · φ ⊢ ψ →
                      ----------------
                      Γ · φ ⊢ ψ

contraction-ND-left = {!   !}

contraction-ND-right : ∀ Δ →
                      Γ ⊢ ⋁ (Δ · φ · φ) →
                      --------------------
                      Γ ⊢ ⋁ (Δ · φ)

contraction-ND-right = {!   !}
```

Reasoning by case split:

```
case-split :
  Γ · φ ⊢ ψ →
  Γ · φ ⇒ ⊥ ⊢ ψ →
  ----------------
  Γ ⊢ ψ

case-split {Γ} {φ} {ψ} Γ·φ⊢ψ Γ·φ⇒⊥⊢ψ = 
  BEGIN
  have Γ · φ ⊢ ψ                          by Γ·φ⊢ψ
  have Γ ⊢ φ ⇒ ψ                          apply ⇒I at here

  have Γ · φ ⇒ ⊥ ⊢ ψ                      by Γ·φ⇒⊥⊢ψ
  have Γ ⊢ (φ ⇒ ⊥) ⇒ ψ                    apply ⇒I at here

  have Γ ⊢ (φ ⇒ ψ) ⇒ ((φ ⇒ ⊥) ⇒ ψ) ⇒ ψ    by hilbert→ND B3
  have Γ ⊢ ((φ ⇒ ⊥) ⇒ ψ) ⇒ ψ              apply ⇒E at here , back 3
  have Γ ⊢ ψ                              apply ⇒E at here , back 2
  END
```

Bring a disjunct to the left by negating it:

```
swap-Neg-Or-ND : Γ ⊢ φ ∨ ψ →
                 --------------
                 Γ · ψ ⇒ ⊥ ⊢ φ

swap-Neg-Or-ND {Γ} {φ} {ψ} Γ⊢φ∨ψ =
  BEGIN
    have Γ ⊢ φ ∨ ψ              by Γ⊢φ∨ψ
    have Γ ⊆ Γ · ψ ⇒ ⊥          by there
    have Γ · ψ ⇒ ⊥ ⊢ φ ∨ ψ      apply weakening-ND at back 1 , here

    have Γ · ψ ⇒ ⊥ · φ ⊢ φ      by Ass here

    have Γ · ψ ⇒ ⊥ · ψ ⊢ ψ ⇒ ⊥  by Ass back 1
    have Γ · ψ ⇒ ⊥ · ψ ⊢ ψ      by Ass here
    have Γ · ψ ⇒ ⊥ · ψ ⊢ ⊥      apply ⇒E at back 1 , here
    have Γ · ψ ⇒ ⊥ · ψ ⊢ φ      apply ⊥E at here

    have Γ · ψ ⇒ ⊥ ⊢ φ          apply ∨E at back 5 , back 4 , here
  END
```

```
commOr-ND : Γ ⊢ (φ ∨ ψ) ⇒ (ψ ∨ φ)

commOr-ND {Γ} {φ} {ψ} =
  BEGIN
    have Γ · φ ∨ ψ ⊢ φ ∨ ψ            by Ass here
    have Γ · φ ∨ ψ · ψ ⊢ND ψ          by Ass here
    have Γ · φ ∨ ψ · ψ ⊢ND ψ ∨ φ      apply ∨I-left at here
    have Γ · φ ∨ ψ · φ ⊢ND φ          by Ass here
    have Γ · φ ∨ ψ · φ ⊢ND ψ ∨ φ      apply ∨I-right at here
    have Γ · φ ∨ ψ ⊢ ψ ∨ φ            apply ∨E at back 4 , here , back 2
    have Γ ⊢ (φ ∨ ψ) ⇒ (ψ ∨ φ)        apply DT2-ND at here
  END

assocOr-ND : Γ ⊢ φ ∨ ψ ∨ ξ →
             -----------------
             Γ ⊢ (φ ∨ ψ) ∨ ξ

assocOr-ND {Γ} {φ} {ψ} {ξ} Γ⊢φ∨ψ∨ξ =
  BEGIN
    have Γ ⊢ φ ∨ ψ ∨ ξ                  by Γ⊢φ∨ψ∨ξ

    have Γ · φ ⊢ φ                      by Ass here
    have Γ · φ ⊢ (φ ∨ ψ) ∨ ξ            apply ∨I-left ∘ ∨I-left at here

    have Γ · ψ ∨ ξ · ψ ⊢ ψ              by Ass here
    have Γ · ψ ∨ ξ · ψ ⊢ (φ ∨ ψ) ∨ ξ    apply ∨I-left ∘ ∨I-right at here
    have Γ · ψ ∨ ξ · ξ ⊢ ξ              by Ass here
    have Γ · ψ ∨ ξ · ξ ⊢ (φ ∨ ψ) ∨ ξ    apply ∨I-right at here
    have Γ · ψ ∨ ξ ⊢ ψ ∨ ξ              by Ass here
    have Γ · ψ ∨ ξ ⊢ (φ ∨ ψ) ∨ ξ        apply ∨E at here , back 3 , back 1

    have Γ ⊢ (φ ∨ ψ) ∨ ξ                apply ∨E at back 8 , back 6 , here
  END

attachOr-ND : Γ ⊢ φ ∨ ψ →
              Γ ⊢ φ ⇒ ξ →
              -----------
              Γ ⊢ ξ ∨ ψ

attachOr-ND {Γ} {φ} {ψ} {ξ} Γ⊢φ∨ψ Γ⊢φ⇒ξ =
  BEGIN
  have Γ ⊢ φ ∨ ψ        by Γ⊢φ∨ψ
  have Γ ⊢ φ ⇒ ξ        by Γ⊢φ⇒ξ
  have Γ ⊢ ξ ∨ ψ        by {!   !}
  END


    -- have Γ · ψ ⊢ND ψ                                by Ass here
    -- have Γ · ψ ⊢ND (φ ∨ ψ) ∨ (⋁ Ξ)                  apply ∨I-left ∘ ∨I-right at here

    -- have Γ · φ ∨ (⋁ Ξ) ⊢ND φ ∨ (⋁ Ξ)                by Ass here
    -- have Γ · φ ∨ (⋁ Ξ) · φ ⊢ND φ                    by Ass here
    -- have Γ · φ ∨ (⋁ Ξ) · φ ⊢ND (φ ∨ ψ) ∨ (⋁ Ξ)      apply ∨I-left ∘ ∨I-left at here
    -- have Γ · φ ∨ (⋁ Ξ) · (⋁ Ξ) ⊢ND ⋁ Ξ              by Ass here
    -- have Γ · φ ∨ (⋁ Ξ) · (⋁ Ξ) ⊢ND (φ ∨ ψ) ∨ (⋁ Ξ)  apply ∨I-right at here
    -- have Γ · φ ∨ (⋁ Ξ) ⊢ND (φ ∨ ψ) ∨ (⋁ Ξ)          apply ∨E at back 4 , back 2 , here
    -- have Γ ⊢ND (φ ∨ ψ) ∨ (⋁ Ξ)


longDisjunction-++-ND : ∀ Ψ → 
                        Γ ⊢ (⋁ Ψ) ∨ (⋁ Ξ) →
                        --------------------
                        Γ ⊢ ⋁ (Ψ ++ Ξ)

longDisjunction-++-ND {Γ} {Ξ} Ψ Γ⊢Ψ∨Ξ = {!   !}
```


# Preparation for sequent calculus

We show some reasoning rules which will be helpful in studying sequent calculus.

```
∧-left-ND : Γ · φ · ψ ⊢ ξ →
            ---------------
            Γ · φ ∧ ψ ⊢ ξ

∧-left-ND {Γ} {φ} {ψ} {ξ} Γφψ⊢ξ = 
  BEGIN
  have Γ · φ ∧ ψ ⊢ φ ∧ ψ        by Ass here
  have Γ · φ ∧ ψ ⊢ φ            apply ∧E-left at here
  have Γ · φ ∧ ψ ⊢ ψ            apply ∧E-right at back 1

  have Γ · φ · ψ ⊢ ξ            by Γφψ⊢ξ
  have Γ ⊢ φ ⇒ ψ ⇒ ξ            apply DT2-ND ∘ DT2-ND at here
  have Γ ⊆ Γ · φ ∧ ψ            by there
  have Γ · φ ∧ ψ ⊢ φ ⇒ ψ ⇒ ξ    apply weakening-ND at back 1 , here
  have Γ · φ ∧ ψ ⊢ ψ ⇒ ξ        apply ⇒E at here , back 5
  have Γ · φ ∧ ψ ⊢ ξ            apply ⇒E at here , back 5
  END

∨-left-ND : Γ · φ ⊢ ξ →
            Γ · ψ ⊢ ξ →
            -------------
            Γ · φ ∨ ψ ⊢ ξ

∨-left-ND {Γ} {φ} {ξ} {ψ} Γ·φ⊢ξ Γ·ψ⊢ξ = 
  BEGIN
  have Γ · φ ⊢ ξ                  by Γ·φ⊢ξ
  have Γ · φ ⊆ Γ · φ ∨ ψ · φ      by (λ{ here → here; (there x) → there (there x)}) -- can this be automated?
  have Γ · φ ∨ ψ · φ ⊢ ξ          apply weakening-ND at back 1 , here

  have Γ · ψ ⊢ ξ                  by Γ·ψ⊢ξ
  have Γ · ψ ⊆ Γ · φ ∨ ψ · ψ      by (λ{ here → here; (there x) → there (there x)}) -- can this be automated?
  have Γ · φ ∨ ψ · ψ ⊢ ξ          apply weakening-ND at back 1 , here

  have Γ · φ ∨ ψ ⊢ φ ∨ ψ          by Ass here
  have Γ · φ ∨ ψ ⊢ ξ              apply ∨E at here , back 4 , back 1
  END

⇒-left-ND : Γ ⊢ φ ∨ ξ →
            Γ · ψ ⊢ θ →
            -------------------
            Γ · φ ⇒ ψ ⊢ ξ ∨ θ

⇒-left-ND {Γ} {φ} {ξ} {ψ} {θ} = {!   !}

    -- have Γ ⊢ND φ ∨ (⋁ Ψ)                    by Γ⊢NDΔ·φ
    -- have Γ ⊆ Γ · φ ⇒ ψ                      by there
    -- have Γ · φ ⇒ ψ ⊢ND φ ∨ (⋁ Ψ)            apply weakening-ND at back 1 , here
    -- have Γ · φ ⇒ ψ ⊢ND φ ⇒ ψ                by Ass here
    -- have Γ · φ ⇒ ψ ⊢ND ψ ∨ (⋁ Ψ)            by ? -- apply ⇒E at here , back 1

    -- have Γ · ψ ⊢ND ⋁ Ξ                      by Γ·ψ⊢NDΞ
    -- have Γ ⊢ND ψ ⇒ (⋁ Ξ)                    apply DT2-ND at here
    
    -- have Γ · φ ⇒ ψ ⊢ND ψ ⇒ (⋁ Ξ)            apply weakening-ND at here , back 5
    -- have Γ · φ ⇒ ψ ⊢ND ⋁ Ξ                  apply ⇒E at here , back 3

    -- have Γ · φ ⇒ ψ ⊢ND (⋁ Ψ) ∨ (⋁ Ξ)        by ?

    -- have Γ · φ ⇒ ψ ⊢ND ⋁ (Ψ ++ Ξ)           by {!   !} -- apply ⇒E at here , back 3

⇒-right-ND : Γ · φ ⊢ ψ ∨ ξ →
             ---------------
             Γ ⊢ (φ ⇒ ψ) ∨ ξ

⇒-right-ND {Γ} {φ} {ψ} {ξ} Γ·φ⊢ψ∨ξ = 
  BEGIN
    have Γ · φ ⊢ ψ ∨ ξ              by Γ·φ⊢ψ∨ξ

    have Γ · φ · ψ · φ ⊢ ψ          by Ass back 1
    have Γ · φ · ψ ⊢ φ ⇒ ψ          apply DT2-ND at here
    have Γ · φ · ψ ⊢ (φ ⇒ ψ) ∨ ξ    apply ∨I-left at here

    have Γ · φ · ξ ⊢ ξ              by Ass here
    have Γ · φ · ξ ⊢ (φ ⇒ ψ) ∨ ξ    apply ∨I-right at here

    have Γ · φ ⊢ (φ ⇒ ψ) ∨ ξ        apply ∨E at back 5 , back 2 , here

    have Γ · φ ⇒ ⊥ · φ ⊢ φ ⇒ ⊥      by Ass back 1
    have Γ · φ ⇒ ⊥ · φ ⊢ φ          by Ass here
    have Γ · φ ⇒ ⊥ · φ ⊢ ⊥          apply ⇒E at back 1 , here
    have Γ · φ ⇒ ⊥ · φ ⊢ ψ          apply ⊥E at here

    have Γ · φ ⇒ ⊥ ⊢ φ ⇒ ψ          apply DT2-ND at here
    have Γ · φ ⇒ ⊥ ⊢ (φ ⇒ ψ) ∨ ξ    apply ∨I-left at here

    have Γ ⊢ (φ ⇒ ψ) ∨ ξ            apply case-split at back 6 , here
  END

⇔-left-ND : Γ ⊢ ψ ∨ φ →
            Γ · φ · ψ ⊢ ξ →
            ----------------
            Γ · φ ⇔ ψ ⊢ ξ

⇔-left-ND {Γ} {ψ} {φ} {ξ} Γ⊢φ∨ψ Γ·φ·ψ⊢ξ =
  BEGIN
    have Γ ⊢ ψ ∨ φ                      by Γ⊢φ∨ψ
    have Γ ⊆ Γ · φ ⇔ ψ                  by there
    have Γ · φ ⇔ ψ ⊢ ψ ∨ φ              apply weakening-ND at back 1 , here

    have Γ · φ · ψ ⊢ ξ                  by Γ·φ·ψ⊢ξ
    have Γ ⊢ φ ⇒ ψ ⇒ ξ                  apply DT2-ND ∘ DT2-ND at here
    have Γ · φ ⇔ ψ ⊢ φ ⇒ ψ ⇒ ξ          apply weakening-ND at here , back 3

    have Γ · φ ⇔ ψ ⊢ φ ⇔ ψ              by Ass here
    have Γ · φ ⇔ ψ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)  apply ⇔E at here
    have Γ · φ ⇔ ψ ⊢ φ ⇒ ψ              apply ∧E-left at here
    have Γ · φ ⇔ ψ ⊢ ψ ⇒ φ              apply ∧E-right at back 1

    have Γ · φ ⇔ ψ ⊆ Γ · φ ⇔ ψ · φ      by there
    have Γ · φ ⇔ ψ · φ ⊢ φ ⇒ ψ          apply weakening-ND at back 2 , here
    have Γ · φ ⇔ ψ · φ ⊢ φ              by Ass here
    have Γ · φ ⇔ ψ · φ ⊢ ψ              apply ⇒E at back 1 , here
    have Γ · φ ⇔ ψ · φ ⊢ φ ⇒ ψ ⇒ ξ      apply weakening-ND at back 8 , back 3
    have Γ · φ ⇔ ψ · φ ⊢ ψ ⇒ ξ          apply ⇒E at here , back 2
    have Γ · φ ⇔ ψ · φ ⊢ ξ              apply ⇒E at here , back 2

    have Γ · φ ⇔ ψ ⊆ Γ · φ ⇔ ψ · ψ      by there
    have Γ · φ ⇔ ψ · ψ ⊢ ψ ⇒ φ          apply weakening-ND at back 8 , here
    have Γ · φ ⇔ ψ · ψ ⊢ ψ              by Ass here
    have Γ · φ ⇔ ψ · ψ ⊢ φ              apply ⇒E at back 1 , here
    have Γ · φ ⇔ ψ · ψ ⊢ φ ⇒ ψ ⇒ ξ      apply weakening-ND at back 15 , back 3
    have Γ · φ ⇔ ψ · ψ ⊢ ψ ⇒ ξ          apply ⇒E at here , back 1
    have Γ · φ ⇔ ψ · ψ ⊢ ξ              apply ⇒E at here , back 3

    have Γ · φ ⇔ ψ ⊢ ξ                  apply ∨E at back 21 , here , back 7
  END

⇔-left'-ND : Γ ⊢ ψ ∨ φ ∨ ξ →
             Γ · φ · ψ ⊢ θ →
             -----------------
             Γ · φ ⇔ ψ ⊢ ξ ∨ θ

⇔-left'-ND {Γ} {ψ} {φ} {ξ} {θ} Γ⊢φ∨ψ∨ξ Γ·φ·ψ⊢θ =
  BEGIN
    have Γ ⊢ ψ ∨ φ ∨ ξ                      by Γ⊢φ∨ψ∨ξ
    have Γ ⊢ (ψ ∨ φ) ∨ ξ                    apply assocOr-ND at here
    have Γ ⊆ Γ · φ ⇔ ψ                      by there
    have Γ · φ ⇔ ψ ⊢ (ψ ∨ φ) ∨ ξ            apply weakening-ND at back 1 , here

    have Γ · ψ ∨ φ ⊢ ψ ∨ φ                  by Ass here

    have Γ · φ · ψ ⊢ θ                      by Γ·φ·ψ⊢θ
    have Γ · φ · ψ ⊆ Γ · ψ ∨ φ · φ · ψ      by (λ{here → here
                                                ; (there here) → there here
                                                ; (there (there x)) → there (there (there x))})
    have Γ · ψ ∨ φ · φ · ψ ⊢ θ              apply weakening-ND at back 1 , here
    have Γ · ψ ∨ φ · φ ⇔ ψ ⊢ θ              apply ⇔-left-ND at back 3 , here
    have Perm (Γ · ψ ∨ φ · φ ⇔ ψ)
              (Γ · φ ⇔ ψ · ψ ∨ φ)           by swap stop
    have Γ · φ ⇔ ψ · ψ ∨ φ ⊢ θ              apply perm-ND-left at here , back 1
    have Γ · φ ⇔ ψ · ψ ∨ φ ⊢ ξ ∨ θ          apply ∨I-right at here

    have Γ · φ ⇔ ψ · ξ ⊢ ξ ∨ θ              by ∨I-left (Ass here)

    have Γ · φ ⇔ ψ ⊢ ξ ∨ θ                  apply ∨E at back 9 , back 1 , here
  END

 

↔-right-ND : Γ · φ ⊢ ψ →
             Γ · ψ ⊢ φ →
             --------------
             Γ ⊢ φ ⇔ ψ

↔-right-ND {Γ} {φ} {ψ} Γ·φ⊢ψ Γ·ψ⊢φ =
  BEGIN
  have Γ · φ ⊢ ψ              by Γ·φ⊢ψ
  have Γ ⊢ φ ⇒ ψ              apply DT2-ND at here

  have Γ · ψ ⊢ φ              by Γ·ψ⊢φ
  have Γ ⊢ ψ ⇒ φ              apply DT2-ND at here

  have Γ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)  apply ∧I at back 2 , here
  have Γ ⊢ φ ⇔ ψ              apply ⇔I at here
  END

↔-right'-ND : Γ · φ ⊢ ψ ∨ ξ →
             Γ · ψ ⊢ φ ∨ ξ →
             ----------------
             Γ ⊢ (φ ⇔ ψ) ∨ ξ

↔-right'-ND {Γ} {φ} {ψ} {ξ} Γ·φ⊢ψ∨ξ Γ·ψ⊢φ∨ξ =
  BEGIN
  have Γ · φ ⊢ ψ ∨ ξ                  by Γ·φ⊢ψ∨ξ
  have Γ ⊢ (φ ⇒ ψ) ∨ ξ                apply ⇒-right-ND at here
  have Γ · ξ ⇒ ⊥ ⊢ φ ⇒ ψ              apply swap-Neg-Or-ND at here

  have Γ · ψ ⊢ φ ∨ ξ                  by Γ·ψ⊢φ∨ξ
  have Γ ⊢ (ψ ⇒ φ) ∨ ξ                apply ⇒-right-ND at here
  have Γ · ξ ⇒ ⊥ ⊢ ψ ⇒ φ              apply swap-Neg-Or-ND at here

  have Γ · ξ ⇒ ⊥ ⊢ (φ ⇒ ψ) ∧ (ψ ⇒ φ)  apply ∧I at back 3 , here
  have Γ · ξ ⇒ ⊥ ⊢ φ ⇔ ψ              apply ⇔I at here
  have Γ · ξ ⇒ ⊥ ⊢ (φ ⇔ ψ) ∨ ξ        apply ∨I-left at here

  have Γ · ξ ⊢ ξ                      by Ass here
  have Γ · ξ ⊢ (φ ⇔ ψ) ∨ ξ            apply ∨I-right at here

  have Γ ⊢ (φ ⇔ ψ) ∨ ξ                apply case-split at here , back 2
  END

cut-ND : Γ ⊢ φ ∨ ψ →
         Γ · φ ⊢ ξ →
         -----------
         Γ ⊢ ψ ∨ ξ

cut-ND {Γ} {φ} {ψ} {ξ} Γ⊢φ∨ψ Γ·φ⊢ξ =
  BEGIN
    have Γ ⊢ φ ∨ ψ           by Γ⊢φ∨ψ

    have Γ · φ ⊢ ξ           by Γ·φ⊢ξ
    have Γ · φ ⊢ ψ ∨ ξ       apply ∨I-right at here

    have Γ · ψ ⊢ ψ            by Ass here
    have Γ · ψ ⊢ ψ ∨ ξ        apply ∨I-left at here

    have Γ ⊢ ψ ∨ ξ           apply ∨E at back 4 , back 2 , here
  END


```