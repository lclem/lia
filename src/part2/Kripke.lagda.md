---
title: "Kripke models for intuitionistic propositional logic 🚧"
---

Literature:

* C.f. @Dosen:APAL:1993 for a weaker notion of Kripke models (*rudimentary Kripke models*),
for which the calculus is proved strongly sound and complete.

```
{-# OPTIONS --allow-unsolved-metas  #-}
open import part0.index hiding (_⊑_; refl-⊑; trans-⊑; antisym-⊑)

module part2.Kripke (n' : ℕ) where
open import part2.NaturalDeduction n' public
```

# Kripke structures

```
record Kripke : Set1 where
  field

    -- possible worlds
    W : Set

    -- accessibility relation
    _⊑_ : W → W → Set

    -- the accessibility relation is a partial order on W
    refl-⊑ : ∀ w → w ⊑ w
    trans-⊑ : ∀ u v w → u ⊑ v → v ⊑ w → u ⊑ w
    antisym-⊑ : ∀ u v → u ⊑ v → v ⊑ u → u ≡ v

    -- local truth valuation
    ⟦_⟧_ : PropName → W → Set

    -- the truth valuation is monotone
    mon-⟦⟧ : ∀ p u v → u ⊑ v → ⟦ p ⟧ u → ⟦ p ⟧ v

open Kripke {{...}} public
```

## Forcing relation

```
_⊨_ : ∀ {{K : Kripke}} → W → Formula → Set
w ⊨ ⊤ = T
w ⊨ ⊥ = F
w ⊨ (` p) = ⟦ p ⟧ w
w ⊨ (φ ∧ ψ) = w ⊨ φ × w ⊨ ψ
w ⊨ (φ ∨ ψ) = w ⊨ φ ⊎ w ⊨ ψ
w ⊨ (φ ⇒ ψ) = ∀ (u : W) → w ⊑ u → u ⊨ φ → u ⊨ ψ
```

Useful when we need to mention the structure explicitly.

```
_/_⊨_ : ∀ (K : Kripke) → W {{K}} → Formula → Set
K / w ⊨ φ = _⊨_ {{K}} w φ
```

The semantics for negation says that `φ` does not hold in the current world as a special case

```
¬-now : ∀ {{K : Kripke}} (w : W) φ → w ⊨ ¬ φ → ~ (w ⊨ φ)
¬-now w φ w⊨¬φ w⊨φ = w⊨¬φ w (refl-⊑ _) w⊨φ 
```

## Tautologies

```
Tautology : Formula → Set1
Tautology φ = ∀ {{K : Kripke}} (w : W) → w ⊨ φ
```

## Monotonicity

The local semantics function `⟦_⟧_` is monotone by assumption.
We show that this extends to the whole semantics `_⊨_`.

```
mon-⊨ : ∀ {{_ : Kripke}} φ (u v : W) → u ⊑ v → u ⊨ φ → v ⊨ φ

mon-⊨ ⊤ u v u⊑v u⊨φ = tt

mon-⊨ (` p) u v u⊑v u⊨φ = mon-⟦⟧ p u v u⊑v u⊨φ

mon-⊨ (φ ∧ ψ) u v u⊑v (u⊨φ , u⊨ψ) with mon-⊨ φ _ _ u⊑v u⊨φ | mon-⊨ ψ _ _ u⊑v u⊨ψ
... | v⊨φ | v⊨ψ = v⊨φ , v⊨ψ

mon-⊨ (φ ∨ ψ) u v u⊑v (left u⊨φ) = left (mon-⊨ φ _ _ u⊑v u⊨φ)
mon-⊨ (φ ∨ ψ) u v u⊑v (right u⊨ψ) = right (mon-⊨ ψ _ _ u⊑v u⊨ψ)

mon-⊨ (φ ⇒ ψ) u v u⊑v u⊨φ⇒ψ w v⊑w = u⊨φ⇒ψ w (trans-⊑ _ _ _ u⊑v v⊑w)
```

## Soundness

```
_⊧_ : Context → Formula → Set1
Γ ⊧ φ = ∀ {{K : Kripke}} (w : W) → (∀ ψ → ψ ∈ Γ → w ⊨ ψ) → w ⊨ φ

soundness : ∀ Γ φ → Γ ⊢ φ → Γ ⊧ φ

soundness Γ φ (A φ∈Γ) w memb = memb _ φ∈Γ

soundness Γ φ ⊤I w memb = tt

soundness Γ (φ ⇒ ψ) (⇒I Γ,φ⊢ψ) w memb u w⊑u w⊨φ = soundness _ _ Γ,φ⊢ψ u λ{ ξ here → w⊨φ ; ξ (there ξ∈Γ) → mon-⊨ ξ _ _ w⊑u (memb _ ξ∈Γ) }

soundness Γ ψ (⇒E Γ⊢φ⇒ψ Γ⊢φ) w memb with soundness Γ _ Γ⊢φ⇒ψ w memb | soundness Γ _ Γ⊢φ w memb
... | indφ⇒ψ | indφ = indφ⇒ψ w (refl-⊑ w) indφ

soundness Γ (φ ∧ ψ) (∧I Γ⊢φ Γ⊢ψ) w memb with
  soundness Γ φ Γ⊢φ w memb | soundness Γ ψ Γ⊢ψ w memb
... | w⊨φ | w⊨ψ = w⊨φ , w⊨ψ

soundness Γ _ (∧E-left Γ⊢φ∧ψ) w memb
  with soundness Γ _ Γ⊢φ∧ψ w memb
... | w⊨φ , w⊨ψ = w⊨φ

soundness Γ _ (∧E-right Γ⊢φ∧ψ) w memb
  with soundness Γ _ Γ⊢φ∧ψ w memb
... | w⊨φ , w⊨ψ = w⊨ψ

soundness Γ _ (∨I-left Γ⊢φ) w memb
  with soundness Γ _ Γ⊢φ w memb
... | w⊨φ = left w⊨φ

soundness Γ _ (∨I-right Γ⊢ψ) w memb
  with soundness Γ _ Γ⊢ψ w memb
... | w⊨ψ = right w⊨ψ

soundness Γ _ (∨E Γ⊢φ∨ψ Γ,φ⊢ξ Γ,ψ⊢ξ) w memb
  with soundness Γ _ Γ⊢φ∨ψ w memb
... | left w⊨φ = soundness (Γ · _) _ Γ,φ⊢ξ w λ{ ξ here → w⊨φ ; ξ (there ξ∈Γ) → memb _ ξ∈Γ }
... | right w⊨ψ = soundness (Γ · _) _ Γ,ψ⊢ξ w λ{ ξ here → w⊨ψ ; ξ (there ξ∈Γ) → memb _ ξ∈Γ }

soundness Γ φ (⊥E Γ⊢⊥) w memb = F-elim (soundness Γ ⊥ Γ⊢⊥ w memb)
```

Weak soundness.

```
weakSoundness : ∀ φ → ∅ ⊢ φ → ∅ ⊧ φ
weakSoundness = {!!}

weakSoundness-contr : ∀ φ (K : Kripke) (w : W {{K}}) → ~ (K / w ⊨ φ) → ~ (∅ ⊢ φ)
weakSoundness-contr φ K w = {!!}
```

# Unprovable formulas

Using soundness we have a method to show that certain formulas are not theorems of intuitionistic propositional logic.
Namely, it suffices to find a Kripke structure and a world therein where the formula does not hold.

```
unprovable : ∀ {{K : Kripke}} (φ : Formula) (w : W) → ~ (w ⊨ φ) → ~ (∅ ⊢ φ)
unprovable φ w ~w⊨φ ∅⊢φ = ~w⊨φ (soundness ∅ φ ∅⊢φ w λ ψ ())
```

We present some applications.

## Law of excluded middle

For example, we show that the following formula expressing the law of excluded middle
is not provable intuitionistically.

```
lem = ` p₀ ∨ ¬ ` p₀
```

To this end, consider the following two-worlds Kripke structure.

```
data 𝟚 : Set where
  w0 : 𝟚
  w1 : 𝟚

K0 : Kripke
K0 = record {

  W = 𝟚;

  _⊑_ = λ{
    w0 w0 → T ;
    w0 w1 → T ;
    w1 w0 → F ;
    w1 w1 → T };

  refl-⊑ = λ{ w0 → tt ; w1 → tt };

  trans-⊑ = λ{
    w0 w0 w0 _ _ → tt ;
    w0 w0 w1 _ _ → tt ;
    w0 w1 w1 _ _ → tt ;
    w1 w1 w1 _ _ → tt};

  antisym-⊑ = λ{ w0 w0 _ _ → refl ; w1 w1 _ _ → refl };

  ⟦_⟧_ = λ{ p₀ w0 → F;
            p₀ w1 → T};

  mon-⟦⟧ = λ{ p₀ w1 w1 _ _ → tt }

  }
```

Now we show that the formula `lem` does not hold in the structure `K0`.

```
~K0⊨lem : ~ (_⊨_ {{K0}} w0 lem)
~K0⊨lem (left w0⊨p) = w0⊨p
~K0⊨lem (right w0⊨p) = w0⊨p w1 tt tt

~⊢lem : ~ (∅ ⊢ lem)
~⊢lem = unprovable {{K0}} _ _ ~K0⊨lem
```

### Unprovability of `¬ p ∨ ¬ ¬ p`

```
lem¬ = ¬ ` p₀ ∨ ¬ ¬ ` p₀

data 𝟛 : Set where
  w0 : 𝟛
  w1 : 𝟛
  w2 : 𝟛

K1 : Kripke
K1 = record {

  W = 𝟛;

  _⊑_ = λ{
    w0 w0 → T ;
    w0 w1 → T ;
    w0 w2 → T ;
    w1 w0 → F ;
    w1 w1 → T ;
    w1 w2 → F ;
    w2 w0 → F ;
    w2 w1 → F ;
    w2 w2 → T };

  refl-⊑ = λ{ w0 → tt ; w1 → tt ; w2 → tt };

  trans-⊑ = λ{
    w0 w0 w0 _ _ → tt ;
    w0 w0 w1 _ _ → tt ;
    w0 w0 w2 _ _ → tt ;
    w0 w1 w1 _ _ → tt ;
    w0 w2 w2 _ _ → tt ;
    w1 w1 w1 _ _ → tt ;
    w2 w2 w2 _ _ → tt };

  antisym-⊑ = λ{ w0 w0 _ _ → refl ; w1 w1 _ _ → refl ;  w2 w2 _ _ → refl };

  ⟦_⟧_ = λ{
    p₀ w0 → F ;
    p₀ w1 → T ;
    p₀ w2 → F } ;

  mon-⟦⟧ = λ{ p₀ w1 w1 _ _ → tt; p w0 w0 tt () }

  }
```

```
~K1⊨lem¬ : ~ (_⊨_ {{K1}} w0 lem¬)

-- this holds since p becomes true in w1
~K1⊨lem¬ (left w0⊨¬p) = w0⊨¬p w1 tt tt

-- this holds since p stays forever false in w2
~K1⊨lem¬ (right w0⊨¬¬p) = w0⊨¬¬p w2 tt w2⊨¬p  where

  -- we first establish that ¬p holds in w2
  w2⊨¬p : _⊨_ {{K1}} w2 (¬ ` p₀)
  w2⊨¬p w2 _ x = x

~⊢lem¬ : ~ (∅ ⊢ lem¬)
~⊢lem¬ = unprovable {{K1}} _ _ ~K1⊨lem¬
```

## More examples

Find counter-models for Peirce's law, double negation law, etc...

## Intuitionistic vs. classical tautologies

We show that formulas that hold in all terminal worlds of Kripke models
are precisely the classical tautologies.

This follows from the fact that the local truth assignment `⟦_⟧`
is the same as a truth valuation.




# Decidability

Difficult!

```
--decideIPL-⊨ : ∀ (φ : Formula) → Dec (∅ ⊨ φ)
--decideIPL-⊨ = {!!}
```

