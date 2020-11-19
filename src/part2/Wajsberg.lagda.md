---
title: Wajsberg's algorithm
---

```
{-# OPTIONS --allow-unsolved-metas #-}

open import part0.index

module part2.Wajsberg (n' : ℕ) where
open import part2.NaturalDeduction n' public hiding (_·_)
```

WARNING: two tests are failing, there is a bug somewhere...

-- alternatively we could make sure that premises in Γ do not contain top-level conjunctions φ ∧ ψ

```
paths : Formula → (Formula * × Formula) *
paths (φ ∧ ψ) = paths φ ++ paths ψ
paths (φ ⇒ ψ) = map (λ{ (ξs , ξ) → φ ∷ ξs , ξ }) (paths ψ)
paths φ = [ (ε , φ) ]
```

```
DecisionProcedure = ∀ (Γ : Formula *) (φ : Formula) → 𝔹

-- add only if not present already
_·_ : Formula * → Formula → Formula *
Γ · φ with φ ∈? Γ
... | yes _ = Γ
... | no _ = φ ∷ Γ

{-# TERMINATING #-}
wajsberg1 wajsberg1' : ∀ (h : DecisionProcedure) → DecisionProcedure

wajsberg1 h Γ ⊤ = tt

wajsberg1 h Γ (φ ∧ ψ) = h Γ φ ∧𝔹 h Γ ψ

-- this was WRONG!!
-- this is not the only way to prove a disjunction!!
-- we should also check whether (φ ∨ ψ) could be proved by applying the last case
-- now added as wajsberg1' :)
wajsberg1 h Γ (φ ∨ ψ) = h Γ φ ∨𝔹 h Γ ψ ∨𝔹 wajsberg1' h Γ (φ ∨ ψ)

-- for termination it is important that φ is added to Γ
-- only if it is not there already
wajsberg1 h Γ (φ ⇒ ψ) = h (Γ · φ) ψ

-- look for some assumption in Γ of the form φ₁ ⇒ ... ⇒ φn ⇒ φ
-- and prove all premises φ₁, ..., φn
wajsberg1 h Γ φ = wajsberg1' h Γ φ

wajsberg1' h Γ φ = foldl _∨𝔹_ ff (map go allPaths) where --  ++ map go⊥ allPaths) where

  rec : Formula * → 𝔹
  rec φs = foldl _∧𝔹_ tt (map (h Γ) φs)

  allPaths = concatMap paths Γ

  go : Formula * × Formula → 𝔹
  go (φs , ψ ∨ ξ) = rec φs ∧𝔹 h (Γ · ψ) φ ∧𝔹 h (Γ · ξ) φ
  go (φs , ⊥) = rec φs
  go (φs , ψ) with ψ ≡? φ
  ... | yes _ = rec φs
  ... | no _ = ff

  -- go⊥ : (Formula n *) × Formula n → 𝔹
  -- go⊥ ⟨ φs , ⊥ ⟩ = rec φs
  -- go⊥ _ = ff
```

```
{-# TERMINATING #-}
wajsberg2 : ∀ (Γs : Formula * *) → DecisionProcedure
wajsberg2 Γs Γ φ
  with Γ · φ ∈? Γs
... | yes _ = ff -- avoid infinite depth recursion
... | no _ = wajsberg1 (wajsberg2 Δs) Γ φ where

  Δs = (Γ · φ) ∷ Γs

wajsberg : DecisionProcedure
wajsberg = wajsberg2 ε
```

```
_  : wajsberg ([ ⊥ ]) ⊥ ≡ tt
_ = refl
```

# Tests

```
p = ` p₀
q = ` p₁
r = ` p₂

_ : wajsberg ε p ≡ ff
_ = refl

_ : wajsberg ε (¬ p) ≡ ff
_ = refl

_ : wajsberg ([ p ]) ⊥ ≡ ff
_ = refl

_ : wajsberg ε (p ∨ ¬ p) ≡ ff
_ = refl

_ : wajsberg ([ p ]) p ≡ tt
_ = refl
```

```
_ : wajsberg ([ p (¬ p) ]) ⊥ ≡ tt
_ = refl

_ : wajsberg ([ p (p ⇒ q) ]) q ≡ tt
_ = refl

_ : wajsberg ε (p ⇒ ¬ ¬ p) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ p ⇒ p) ≡ ff
_ = refl

_ : wajsberg ε (¬ p ∨ ¬ ¬ p) ≡ ff
_ = refl

_ : wajsberg ε (¬ ¬ (p ∨ ¬ p)) ≡ tt
_ = refl

lem = p ∨ ¬ p
¬lem = ¬ lem

_ : wajsberg ε (¬ (p ∨ q) ⇒ ¬ p ∧ ¬ q) ≡ tt
_ = refl
```

```
_  : wajsberg ([ p (q ⇒ p) ]) p ≡ tt
_ = refl

_  : wajsberg ([ p (p ⇒ ⊥) ]) ⊥ ≡ tt
_ = refl

_  : wajsberg ([ p (p ⇒ ⊥) ]) p ≡ tt
_ = refl

_  : wajsberg ([ p (p ⇒ ⊥) ]) q ≡ tt
_ = refl
```

```
_  : wajsberg ε (¬ ¬ p ∨ ¬ ¬ ¬ p) ≡ ff
_ = refl

_ : wajsberg ε ((¬ p ∧ ¬ q) ⇒ ¬ (p ∨ q)) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ ((¬ ¬ p) ⇒ p)) ≡ tt
_ = {! refl !} -- FAILS!

_ : wajsberg ε (¬ ¬ p ∧ ¬ ¬ q ⇔ ¬ ¬ (p ∧ q)) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ (p ∧ q) ⇒ ¬ ¬ p) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ (p ∧ q) ⇒ ¬ ¬ q) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ p ∨ ¬ ¬ q ⇒ ¬ ¬ (p ∨ q)) ≡ tt
_ = refl

_ : wajsberg ε ( ¬ ¬ (p ∨ q) ⇒ ¬ ¬ p ∨ ¬ ¬ q) ≡ ff
_ = refl

_ : wajsberg ε ((¬ ¬ p ⇒ ¬ ¬ q) ⇔ ¬ ¬ (p ⇒ q)) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ p ∧ (¬ ¬ (p ⇒ q)) ⇒ ¬ ¬ q) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ p ⇒ (¬ ¬ p ∨ ¬ ¬ q)) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ q ⇒ (¬ ¬ p ∨ ¬ ¬ q)) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ (p ∨ q) ∧ (¬ ¬ p ⇒ ¬ ¬ r) ∧ (¬ ¬ q ⇒ ¬ ¬ r) ⇒ ¬ ¬ r) ≡ tt
_ = refl

_ : wajsberg ε (¬ ¬ ⊥ ⇒ ¬ ¬ p) ≡ tt
_ = {! refl !} -- FAILS!
```

```
_ : wajsberg ε (((p ⇔ q) ⇔ r) ⇔ (p ⇔ (q ⇔ r))) ≡ ff
_ = refl
```

