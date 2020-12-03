---
title: "Gentzen's natural deduction 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas  #-}

open import part0.index

module part1.NaturalDeduction (n' : ℕ) where
open import part1.Hilbert n' renaming (_⊢_ to _⊢H_) hiding (mon-⊢; soundness)

private
  variable
    p q r : PropName
    φ ψ θ ξ : Formula
    Γ Δ : Context
```

# Natural deduction proofs

```
infixr 5 _⊢_
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
  -- have Γ · ¬ φ · φ ⊢ ¬ φ    by Ass _
  -- have Γ · ¬ φ · φ ⊢ φ ⇒ ⊥  apply ¬E at _
  -- have Γ · ¬ φ · φ ⊢ φ      by _
  -- have Γ · ¬ φ · φ ⊢ ⊥      apply ⇒E at _
  -- have Γ ⊢ ¬ φ ⇒ φ ⇒ ⊥      apply ⇒I ∘ ⇒I at _
  have Γ · ¬ φ · φ ⊢ ¬ φ    by-magic
  have Γ · ¬ φ · φ ⊢ φ ⇒ ⊥  by-magic
  have Γ · ¬ φ · φ ⊢ φ      by-magic
  have Γ · ¬ φ · φ ⊢ ⊥      by-magic
  have Γ ⊢ ¬ φ ⇒ φ ⇒ ⊥      by-magic
  END
```

## Monotonicity

```
mon-⊢ weakening : Δ ⊢ φ → Δ ⊆ Γ → Γ ⊢ φ
mon-⊢ {Δ} {φ} {Γ} (Ass φ∈Δ) Δ⊆Γ = Ass(Δ⊆Γ φ∈Δ)
mon-⊢ {Δ} {.⊤} {Γ} ⊤I Δ⊆Γ = {!   !}
mon-⊢ {Δ} {.(_ ⇒ _)} {Γ} (⇒I Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {φ} {Γ} (⇒E Δ⊢φ Δ⊢φ₁) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {.(_ ∧ _)} {Γ} (∧I Δ⊢φ Δ⊢φ₁) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {φ} {Γ} (∧E-left Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {φ} {Γ} (∧E-right Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {.(_ ∨ _)} {Γ} (∨I-left Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {.(_ ∨ _)} {Γ} (∨I-right Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {φ} {Γ} (∨E Δ⊢φ Δ⊢φ₁ Δ⊢φ₂) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {φ} {Γ} (⊥E Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {φ} {Γ} (⊥⊥E Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {.(¬ _)} {Γ} (¬I Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {.(_ ⇒ ⊥)} {Γ} (¬E Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {.(_ ⇔ _)} {Γ} (⇔I Δ⊢φ) Δ⊆Γ = {!   !}
mon-⊢ {Δ} {.((_ ⇒ _) ∧ (_ ⇒ _))} {Γ} (⇔E Δ⊢φ) Δ⊆Γ = {!   !}

weakening = mon-⊢
```

## Consistency

```
consistent : ~ (∅ ⊢ ⊥)
consistent = {!!}
```

## Deduction theorem

Now this is totally obvious, since it is built into the system:

```
deductionTheorem : Γ · φ ⊢ ψ → Γ ⊢ φ ⇒ ψ
deductionTheorem = ⇒I
```

## Soundness

```
soundness : 
  Γ ⊢ φ →
  -----
  Γ ⊨ φ

soundness {Γ} {φ} Γ⊢NDφ = {!   !}
```

# Soundness and completeness

We show that the rules for natural deduction are sound and complete viAssmutual simulation of Hilbert-style proof system,
and leveraging on the fact that the latter is sound and complete.

For clarity:

```
_⊢ND_ = _⊢_
```

For soundness, it suffices to show that natural deduction can be simulated by Hilbert-style proofs:

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

Notice how:

* Rule !ref(_⊢_)(⇒I) in natural deduction corresponds to the deduction theorem in Hilbert-style proofs.
* Rule !ref(_⊢_)(⇒E) in natural deduction corresponds to modus ponens in Hilbert-style proofs.

For completeness, it suffices to show that Hilbert-style proofs can be simulated by natural deduction:

```
hilbert→ND :
  Γ ⊢H φ →
  -------
  Γ ⊢ND φ

hilbert→ND {Γ} {φ} (Ass φ∈Γ) = Ass φ∈Γ
hilbert→ND {Γ} {φ ⇒ ψ ⇒ φ} A1 = A1-ND
hilbert→ND {Γ} {(φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ ξ} A2 = A2-ND
hilbert→ND {Γ} {.(((_ ⇒ ⊥) ⇒ ⊥) ⇒ _)} A3 = A3-ND
hilbert→ND {Γ} {⊤} T1 = ⊤I
hilbert→ND {Γ} {.((¬ _) ⇒ (_ ⇒ ⊥))} N1 = N1-ND
hilbert→ND {Γ} {.((_ ⇒ ⊥) ⇒ (¬ _))} N2 = {!   !}
hilbert→ND {Γ} {.(_ ⇒ (_ ∨ _))} D1 = {!   !}
hilbert→ND {Γ} {.(_ ⇒ (_ ∨ _))} D2 = {!   !}
hilbert→ND {Γ} {.((_ ⇒ _) ⇒ ((_ ⇒ _) ⇒ ((_ ∨ _) ⇒ _)))} D3 = {!   !}
hilbert→ND {Γ} {.((_ ∧ _) ⇒ _)} C1 = {!   !}
hilbert→ND {Γ} {.((_ ∧ _) ⇒ _)} C2 = {!   !}
hilbert→ND {Γ} {.(_ ⇒ (_ ⇒ (_ ∧ _)))} C3 = {!   !}
hilbert→ND {Γ} {.((_ ⇔ _) ⇒ (_ ⇒ _))} E1 = {!   !}
hilbert→ND {Γ} {.((_ ⇔ _) ⇒ (_ ⇒ _))} E2 = {!   !}
hilbert→ND {Γ} {.((_ ⇒ _) ⇒ ((_ ⇒ _) ⇒ (_ ⇔ _)))} E3 = {!   !}
hilbert→ND {Γ} {φ} (MP Γ⊢Hφ Γ⊢Hφ₁) = {!   !}
```

