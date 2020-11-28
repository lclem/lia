---
title: "Completeness of Hilbert's proof system for propositional logic 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-} -- --rewriting --confluence-check
open import part0.index

module part1.Completeness (n′ : ℕ) where
open import part1.CharacteristicFormulas n′ hiding (ϱtt; ϱff)

private
  variable
    φ ψ θ ξ : Formula
    Γ Δ : Context
```

References:

* Proof pearl @CaiKaposiAltenkirch:2015 for propositional logic.
* modal logic S5 @Bentzen:arXiv:2019.

# Proof system

```
infixr 5 _⊢_
data _⊢_ : Context → Formula → Set where

  -- assumption
  Ass : φ ∈ Γ → Γ ⊢ φ

  -- axioms for implication
  A1 : Γ ⊢ φ ⇒ ψ ⇒ φ -- projection
  A2 : Γ ⊢ (φ ⇒ ψ ⇒ θ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ θ -- transitivity
  A3 : Γ ⊢ ((φ ⇒ ⊥) ⇒ ⊥) ⇒ φ -- double negation

  -- axioms for disjunction
  D1 : Γ ⊢ φ ⇒ φ ∨ ψ
  D2 : Γ ⊢ ψ ⇒ φ ∨ ψ
  D3 : Γ ⊢ (φ ⇒ θ) ⇒ (ψ ⇒ θ) ⇒ (φ ∨ ψ) ⇒ θ

  -- axioms for conjunction
  C1 : Γ ⊢ φ ∧ ψ ⇒ φ
  C2 : Γ ⊢ φ ∧ ψ ⇒ ψ
  C3 : Γ ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ θ) ⇒ φ ⇒ ψ ∧ θ

  -- axioms for bi-implication
  E1 : Γ ⊢ (φ ⇔ ψ) ⇒ φ ⇒ ψ
  E2 : Γ ⊢ (φ ⇔ ψ) ⇒ ψ ⇒ φ
  E3 : Γ ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ (φ ⇔ ψ)

  -- modus ponens
  MP : Δ ⊢ φ ⇒ ψ →
       Δ ⊢ φ →
       -----
       Δ ⊢ ψ
```


```
MP2 : Γ ⊢ φ ⇒ ψ ⇒ ξ →
      Γ ⊢ φ →
      Γ ⊢ ψ →
      ------
      Γ ⊢ ξ

MP2 = {!   !}

MP3 : Γ ⊢ φ ⇒ ψ ⇒ ξ ⇒ θ →
      Γ ⊢ φ →
      Γ ⊢ ψ →
      Γ ⊢ ξ →
      ------
      Γ ⊢ θ

MP3 = {!   !}
```

A proof example.

```
B0 : Δ ⊢ φ ⇒ φ
B0 {Δ} {φ} = S5 where

  S1 : Δ ⊢ φ ⇒ φ ⇒ φ
  S1 = A1

  S2 : Δ ⊢ φ ⇒ (φ ⇒ φ) ⇒ φ
  S2 = A1

  S3 : Δ ⊢ (φ ⇒ (φ ⇒ φ) ⇒ φ) ⇒ (φ ⇒ φ ⇒ φ) ⇒ φ ⇒ φ
  S3 = A2

  S4 : Δ ⊢ (φ ⇒ φ ⇒ φ) ⇒ φ ⇒ φ
  S4 = MP S3 S2

  S5 : Δ ⊢ φ ⇒ φ
  S5 = MP S4 S1
```

## Monotonicity

```
mon-⊢ : Δ ⊢ φ → Δ · ψ ⊢ φ
mon-⊢ (Ass φ∈Δ) = Ass (there φ∈Δ)

mon-⊢ A1 = A1
mon-⊢ A2 = A2
mon-⊢ A3 = A3

mon-⊢ D1 = D1
mon-⊢ D2 = D2
mon-⊢ D3 = D3

mon-⊢ C1 = C1
mon-⊢ C2 = C2
mon-⊢ C3 = C3

mon-⊢ E1 = E1
mon-⊢ E2 = E2
mon-⊢ E3 = E3

mon-⊢ (MP Δ⊢φ Δ⊢ψ) = MP (mon-⊢ Δ⊢φ) (mon-⊢ Δ⊢ψ)

mon2-⊢ : Δ ⊢ φ → Δ · ψ · ξ ⊢ φ
mon2-⊢ = {!   !}
```

## Deduction theorem

```
dt1 : Δ ⊢ φ ⇒ ψ →
      ---------
      Δ · φ ⊢ ψ

dt1 {Δ} {φ} {ψ} Δ⊢φ⇒ψ = MP Δ,φ⊢φ⇒ψ Δ,φ⊢φ where

  Δ,φ⊢φ⇒ψ : φ ∷ Δ ⊢ φ ⇒ ψ
  Δ,φ⊢φ⇒ψ = mon-⊢ {ψ = φ} Δ⊢φ⇒ψ

  Δ,φ⊢φ : φ ∷ Δ ⊢ φ
  Δ,φ⊢φ = Ass here

dt2 : Δ · φ ⊢ ψ →
      ----------
      Δ ⊢ φ ⇒ ψ

dt2 (Ass here) = B0
dt2 (Ass (there ψ∈Δ)) = MP A1 (Ass ψ∈Δ)
dt2 A1 = MP A1 A1
dt2 A2 = MP A1 A2
dt2 A3 = MP A1 A3

dt2 D1 = MP A1 D1
dt2 D2 = MP A1 D2
dt2 D3 = MP A1 D3

dt2 C1 = MP A1 C1
dt2 C2 = MP A1 C2
dt2 C3 = MP A1 C3

dt2 E1 = MP A1 E1
dt2 E2 = MP A1 E2
dt2 E3 = MP A1 E3

dt2 {Δ} {φ} {ψ} (MP {φ = ξ} φ,Δ⊢ξ⇒ψ φ,Δ⊢ξ) = SS where

  S1 : Δ ⊢ φ ⇒ ξ
  S1 = dt2 φ,Δ⊢ξ

  S2 : Δ ⊢ φ ⇒ ξ ⇒ ψ
  S2 = dt2 φ,Δ⊢ξ⇒ψ

  S3 : Δ ⊢ (φ ⇒ ξ) ⇒ φ ⇒ ψ
  S3 = MP A2 S2

  SS : Δ ⊢ φ ⇒ ψ
  SS = MP S3 S1
```

We inductively extend the deduction theorem to finite sequences of assumptions.

```
deductionTheorem : ε ⊢ Δ Imply φ → Δ ⊢ φ
deductionTheorem {ε} ε⊢ΔImplyφ = ε⊢ΔImplyφ
deductionTheorem {ψ ∷ Δ} {φ} ε⊢ΔImply[ψ⇒φ]
  with deductionTheorem {Δ} {ψ ⇒ φ} ε⊢ΔImply[ψ⇒φ]
... | ind = dt1 ind
```

## Example theorems

```
-- ex falso
B1 : ∀ Δ φ → Δ ⊢ ⊥ ⇒ φ
B1 Δ φ = Δ⊢⊥⇒φ where

  Δ1 : Context
  Δ1 = Δ · ⊥ · φ ⇒ ⊥
  Δ2 = Δ · ⊥
  
  Δ1⊢⊥ : Δ1 ⊢ ⊥
  Δ1⊢⊥ = Ass (there here)

  Δ2⊢¬¬φ : Δ2 ⊢ (φ ⇒ ⊥) ⇒ ⊥
  Δ2⊢¬¬φ = dt2 Δ1⊢⊥

  Δ2⊢φ : Δ2 ⊢ φ
  Δ2⊢φ = MP A3 Δ2⊢¬¬φ

  Δ⊢⊥⇒φ : Δ ⊢ ⊥ ⇒ φ
  Δ⊢⊥⇒φ = dt2 Δ2⊢φ

-- a much simpler proof ;p
B2 : ∀ Δ φ → Δ ⊢ (φ ⇒ ⊥) ⇒ φ ⇒ ⊥
B2 Δ φ = B0 {- dt2 (dt2 Γ₀⊢⊥)  where

   Γ₀ : Context
   Γ₀ = Δ · φ ⇒ ⊥ · φ

   Γ₀⊢φ : Γ₀ ⊢ φ
   Γ₀⊢φ = Ass here

   Γ₀⊢¬φ : Γ₀ ⊢ φ ⇒ ⊥
   Γ₀⊢¬φ = Ass (there here)

   Γ₀⊢⊥ : Γ₀ ⊢ ⊥
   Γ₀⊢⊥ = MP Γ₀⊢¬φ Γ₀⊢φ -}
   
-- contradiction
-- used in the core lemma
B3 : ∀ Δ φ ψ → Δ ⊢ (φ ⇒ ⊥) ⇒ φ ⇒ ψ
B3 Δ φ ψ = Δ⊢¬φ⇒φ⇒ψ where

  Γ₀ : Context
  Γ₀ = Δ · φ ⇒ ⊥ · φ

  Γ₀⊢⊥ : Γ₀ ⊢ ⊥
  Γ₀⊢⊥ = dt1 (dt1 (B2 Δ φ))

  Γ₀⊢ψ : Γ₀ ⊢ ψ
  Γ₀⊢ψ = MP (B1 Γ₀ ψ) Γ₀⊢⊥

  Δ⊢¬φ⇒φ⇒ψ : Δ ⊢ (φ ⇒ ⊥) ⇒ φ ⇒ ψ
  Δ⊢¬φ⇒φ⇒ψ = dt2 (dt2 Γ₀⊢ψ)

-- proof by cases
-- used in the second core lemma
B4 : ∀ Δ φ ψ → Δ ⊢ (φ ⇒ ψ) ⇒ ((φ ⇒ ⊥) ⇒ ψ) ⇒ ψ
B4 Δ φ ψ = dt2 (dt2 Δ1⊢ψ) where

  Δ1 Δ2 Δ3 : Context
  Δ1 = (φ ⇒ ⊥) ⇒ ψ ∷ φ ⇒ ψ ∷ Δ
  Δ2 = Δ1 · ψ ⇒ ⊥
  Δ3 = φ ∷ Δ2

  Δ3⊢φ : Δ3 ⊢ φ
  Δ3⊢φ = Ass here
  
  Δ3⊢φ⇒ψ : Δ3 ⊢ φ ⇒ ψ
  Δ3⊢φ⇒ψ = Ass (there (there (there here)))

  Δ3⊢ψ : Δ3 ⊢ ψ
  Δ3⊢ψ = MP Δ3⊢φ⇒ψ Δ3⊢φ
  
  Δ3⊢¬ψ : Δ3 ⊢ ψ ⇒ ⊥
  Δ3⊢¬ψ = Ass (there here)
  
  Δ3⊢⊥ : Δ3 ⊢ ⊥
  Δ3⊢⊥ = MP Δ3⊢¬ψ Δ3⊢ψ

  Δ2⊢¬φ : Δ2 ⊢ φ ⇒ ⊥
  Δ2⊢¬φ = dt2 Δ3⊢⊥

  Δ2⊢¬φ⇒ψ : Δ2 ⊢ (φ ⇒ ⊥) ⇒ ψ
  Δ2⊢¬φ⇒ψ = Ass (there here)

  Δ2⊢ψ : Δ2 ⊢ ψ
  Δ2⊢ψ = MP Δ2⊢¬φ⇒ψ Δ2⊢¬φ

  Δ2⊢¬ψ : Δ2 ⊢ ψ ⇒ ⊥
  Δ2⊢¬ψ = Ass here
  
  Δ2⊢⊥ : Δ2 ⊢ ⊥
  Δ2⊢⊥ = MP Δ2⊢¬ψ Δ2⊢ψ

  Δ1⊢¬¬ψ : Δ1 ⊢ (ψ ⇒ ⊥) ⇒ ⊥
  Δ1⊢¬¬ψ = dt2 Δ2⊢⊥

  Δ1⊢ψ : Δ1 ⊢ ψ
  Δ1⊢ψ = MP A3 Δ1⊢¬¬ψ

-- used in the core lemma
B5 : ∀ Δ φ ψ → Δ ⊢ φ ⇒ (ψ ⇒ ⊥) ⇒ (φ ⇒ ψ) ⇒ ⊥
B5 Δ φ ψ = dt2 (dt2 (dt2 Δ1⊢⊥)) where

  Δ1 : Context
  Δ1 = Δ · φ · ψ ⇒ ⊥ · φ ⇒ ψ

  Δ1⊢φ : Δ1 ⊢ φ
  Δ1⊢φ = Ass (there (there here))

  Δ1⊢φ⇒ψ : Δ1 ⊢ φ ⇒ ψ
  Δ1⊢φ⇒ψ = Ass here

  Δ1⊢ψ : Δ1 ⊢ ψ
  Δ1⊢ψ = MP Δ1⊢φ⇒ψ Δ1⊢φ

  Δ1⊢¬ψ : Δ1 ⊢ ψ ⇒ ⊥
  Δ1⊢¬ψ = Ass (there here)
  
  Δ1⊢⊥ : Δ1 ⊢ ⊥
  Δ1⊢⊥ = MP Δ1⊢¬ψ Δ1⊢ψ

B6 : Γ ⊢ (ψ ⇒ φ) ⇒ ¬ φ ⇒ ¬ ψ
B6 = {!   !}

-- contraposition
B7 : Γ ⊢ (¬ φ ⇒ ¬ ψ) ⇒ ψ ⇒ φ
B7 = {!   !}

```

# Soundness

```
soundness :
  Δ ⊢ φ →
  -----
  Δ ⊨ φ

soundness (Ass ψ∈Δ) ϱ ⟦Δ⟧ = ⟦Δ⟧ ψ∈Δ

soundness {φ = φ ⇒ ψ ⇒ φ} A1 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = (φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ ξ} A2 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ ξ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = ((φ ⇒ ⊥) ⇒ ⊥) ⇒ φ} A3 ϱ _
  with ⟦ φ ⟧ ϱ
... | tt = refl
... | ff = refl

soundness {φ = φ ⇒ ψ ∨ ξ} D1 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ ξ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = φ ⇒ ψ ∨ ξ} D2 ϱ _ 
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ ξ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = (φ ⇒ θ) ⇒ (ψ ⇒ θ) ⇒ (φ ∨ ψ) ⇒ θ} D3 ϱ _ 
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ θ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = φ ∧ ψ ⇒ φ} C1 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = φ ∧ ψ ⇒ ψ} C2 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = (φ ⇒ ψ) ⇒ (φ ⇒ θ) ⇒ φ ⇒ ψ ∧ θ} C3 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ θ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness {φ = (φ ⇔ ψ) ⇒ φ ⇒ ψ} E1 ϱ _ 
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = (φ ⇔ ψ) ⇒ ψ ⇒ φ} E2 ϱ _
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness {φ = (φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ (φ ⇔ ψ)} E3 ϱ _ 
  with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

-- strong soundness of modus ponens
soundness {φ = ψ} (MP {φ = φ} Δ⊢φ⇒ψ Δ⊢φ) ϱ ⟦Δ⟧
  with soundness Δ⊢φ⇒ψ ϱ ⟦Δ⟧ |
       soundness Δ⊢φ ϱ ⟦Δ⟧
... | ⟦φ⇒ψ⟧ϱ≡tt | ⟦φ⟧ϱ≡tt with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
```
# Completeness for the `⇒, ⊥` fragment {#Completeness}

```
infix 51 _^_ _^^_

_^_ : Formula → Val → Formula
φ ^ ϱ = Cond𝔹 φ (φ ⇒ ⊥) (⟦ φ ⟧ ϱ)

_^^_ : Context → Val → Context
φs ^^ ϱ = map (λ φ → φ ^ ϱ) φs

-- list of all variables
vars : Context
vars = map `_ propNames
```

## Core lemma

```
core-lemma : ∀ φ (_ : Formula[⇒,⊥] φ) (ϱ : Val) →
  ------------------
  vars ^^ ϱ  ⊢ φ ^ ϱ
  
core-lemma .⊥ ⊥ ϱ = B0
core-lemma .(` p) (` p) ϱ = Ass p^ϱ∈ass where

  p∈ps : p ∈ propNames
  p∈ps = findPropName p

  `p∈vars : ` p ∈ vars
  `p∈vars =  map-∈ `_ {enumFin _} p∈ps

  p^ϱ∈ass : ` p ^ ϱ ∈ (vars ^^ ϱ)
  p^ϱ∈ass = map-∈ (λ x → x ^ ϱ) {vars} `p∈vars

core-lemma (φ ⇒ ψ) (viewφ ⇒ viewψ) ϱ
  with core-lemma ψ viewψ ϱ | inspect (⟦ ψ ⟧ ϱ)
... | indψ | it tt ⟦ψ⟧ϱ≡tt
  rewrite ⟦ψ⟧ϱ≡tt |
          ⇒𝔹-rewrite-tt-right (⟦ φ ⟧ ϱ) = MP A1 indψ 
... | indψ | it ff ⟦ψ⟧ϱ≡ff rewrite ⟦ψ⟧ϱ≡ff
  with core-lemma φ viewφ ϱ | inspect (⟦ φ ⟧ ϱ)
... | indφ | it tt ⟦φ⟧ϱ≡tt rewrite ⟦φ⟧ϱ≡tt = MP (MP (B5 _ _ _) indφ) indψ
... | indφ | it ff ⟦φ⟧ϱ≡ff rewrite ⟦φ⟧ϱ≡ff = MP (B3 _ _ _) indφ
```

-- B5 : ∀ {n} Δ (φ ψ : Formula n) → Δ ⊢ φ ⇒ ¬ ψ ⇒ ¬ (φ ⇒ ψ)

## Core lemma 2

```
core-lemma2 :
  Formula[⇒,⊥] φ →
  ε ⊨ φ →
  ∀ m ϱ →
  m ≤ n →
  --------------------
  drop m vars ^^ ϱ ⊢ φ

core-lemma2 {φ} viewφ ⊨φ 0 ϱ _ = repl fromCoreLemma (cong (λ C → vars ^^ ϱ ⊢ C) φ^ϱ≡φ) where

  fromCoreLemma : vars ^^ ϱ ⊢ φ ^ ϱ
  fromCoreLemma = core-lemma φ viewφ ϱ

  ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
  ⟦φ⟧ϱ≡tt = ⊨φ ϱ λ ()
  
  φ^ϱ≡φ : φ ^ ϱ ≡ φ
  φ^ϱ≡φ rewrite ⟦φ⟧ϱ≡tt = refl

core-lemma2 {φ} viewφ ⊨φ (suc m) ϱ sucm≤sucn
  with core-lemma2 {φ} viewφ ⊨φ m
... | ind = goal where

  distinct-ps : distinct propNames
  distinct-ps = enumFinDistinct _

  eql : length propNames ≡ n
  eql = enumFinLen n

  lenps>m : length propNames > m
  lenps>m rewrite eql = sucm≤sucn
                       
  v : PropName
  v = get-ne m propNames lenps>m

  v∈ps : v ∈ propNames ! m
  v∈ps = get-ne-∈! _ _ _
  
  ϱtt ϱff : Val
  ϱtt = ϱ [ v ↦ tt ]
  ϱff = ϱ [ v ↦ ff ]

  indtt : drop m vars ^^ ϱtt ⊢ φ
  indtt = ind ϱtt (trans-≤ n≤sucn sucm≤sucn)

  indff : drop m vars ^^ ϱff ⊢ φ
  indff = ind ϱff (trans-≤ n≤sucn sucm≤sucn)

  ϱttv≡tt : ϱtt v ≡ tt
  ϱttv≡tt = update-≡ v

  v^ϱtt≡v : ` v ^ ϱtt ≡ ` v
  v^ϱtt≡v rewrite ϱttv≡tt = refl

  ϱffv≡ff : ϱff v ≡ ff
  ϱffv≡ff = update-≡ v

  v^ϱff≡¬v : ` v ^ ϱff ≡ ` v ⇒ ⊥
  v^ϱff≡¬v rewrite ϱffv≡ff = refl

  drops : drop m propNames ≡ v ∷ drop (suc m) propNames
  drops = drop-cons m propNames lenps>m

  agree : ∀ b → map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agree b = map-Agree _ _ _ agree2 where

    agree2 : Agree (λ p → ` p ^ (ϱ [ v ↦ b ])) (λ p → ` p ^ ϱ) (drop (suc m) propNames)
    agree2 = Agree2-∘ (λ p → Cond𝔹 (` p) (` p ⇒ ⊥)) (ϱ [ v ↦ b ]) ϱ (drop (suc m) propNames) agree1 where

     agree1 : Agree (ϱ [ v ↦ b ]) ϱ (drop (suc m) propNames)
     agree1 {p} p∈dropps = update-≢ v≢p where

       have : ∃[ k ] p ∈ drop (suc m) propNames ! k
       have = ∈→∈! _ _ p∈dropps

       k : ℕ
       k = dfst have

       p∈dropps!k : p ∈ drop (suc m) propNames ! k
       p∈dropps!k = dsnd have

       p∈ps : p ∈ propNames ! (suc m + k)
       p∈ps = drop-∈! p (suc m) _ _ p∈dropps!k

       v≢p : v ≢ p
       v≢p with v ≡? p
       ... | no proof = proof

       -- derive a contradiction
       ... | yes refl with distinct-ps m (suc m + k) v v∈ps p∈ps
       ... | impossible = F-elim (diseq impossible) where

         ineq : m < suc (m + k)
         ineq =  begin<
           m <≤⟨ n<sucn ⟩
           suc m
             ≤⟨ cong-≤ (Suc □) m≤m+k ⟩
           suc (m + k)
           ∎≤ where

             m≤m+k : m ≤ m + k
             m≤m+k = ≤+

         diseq : m ≢ suc (m + k)
         diseq = <→≢ ineq

  agreett : map (λ p → ` p ^ ϱtt) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agreett = agree tt

  agreeff : map (λ p → ` p ^ ϱff) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agreeff = agree ff

  equality : ∀ b → drop m vars ^^ (ϱ [ v ↦ b ]) ≡ Cond𝔹 (` v) (` v ⇒ ⊥) b ∷ drop (suc m) vars ^^ ϱ
  equality b = begin
    drop m vars ^^ (ϱ [ v ↦ b ])
      ≡⟨ cong (λ C → C ^^ (ϱ [ v ↦ b ])) (drop-map _ m propNames) ⟩
    map `_ (drop m propNames) ^^ (ϱ [ v ↦ b ])
      ≡⟨ map-∘ _ _ (drop m propNames) ⟩
    map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop m propNames)
      ≡⟨ cong (map λ p → ` p ^ (ϱ [ v ↦ b ])) drops ⟩
    map (λ p → ` p ^ (ϱ [ v ↦ b ])) (v ∷ drop (suc m) propNames)
      ≡⟨⟩
    (` v ^ (ϱ [ v ↦ b ])) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨⟩
    Cond𝔹 (` v) (` v ⇒ ⊥) (⟦ ` v ⟧ (ϱ [ v ↦ b ])) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨⟩
    Cond𝔹 (` v) (` v ⇒ ⊥) ((ϱ [ v ↦ b ]) v) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨ cong (λ C → Cond𝔹 (` v) (` v ⇒ ⊥) C ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)) (update-≡ v)  ⟩
    ψ₀ ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨ cong (λ C → ψ₀ ∷ C) (agree b) ⟩
    ψ₀ ∷ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
      ≡⟨ cong (λ C → ψ₀ ∷ C) (sym (map-∘ _ _ (drop (suc m) propNames)))  ⟩
    ψ₀ ∷ map `_ (drop (suc m) propNames) ^^ ϱ
      ≡⟨ cong (λ C → ψ₀ ∷ C ^^ ϱ) (sym (drop-map _ (suc m) propNames)) ⟩
    ψ₀ ∷ drop (suc m) vars ^^ ϱ ∎ where

      ψ₀ : Formula
      ψ₀ = Cond𝔹 (` v) (` v ⇒ ⊥) b

  eql-tt : drop m vars ^^ ϱtt ≡ ` v ∷ drop (suc m) vars ^^ ϱ
  eql-tt = equality tt

  eql-ff : drop m vars ^^ ϱff ≡ (` v ⇒ ⊥) ∷ drop (suc m) vars ^^ ϱ
  eql-ff = equality ff

  indtt' : drop (suc m) vars ^^ ϱ · ` v ⊢ φ
  indtt' = repl indtt (cong (λ C → C ⊢ φ) eql-tt)

  indff' : drop (suc m) vars ^^ ϱ · ` v ⇒ ⊥ ⊢ φ
  indff' = repl indff (cong (λ C → C ⊢ φ) eql-ff)

  indtt'' : drop (suc m) vars ^^ ϱ ⊢ ` v ⇒ φ
  indtt'' = dt2 indtt'

  indff'' : drop (suc m) vars ^^ ϱ ⊢ (` v ⇒ ⊥) ⇒ φ
  indff'' = dt2 indff' 

  goal : drop (suc m) vars ^^ ϱ ⊢ φ
  goal = MP (MP (B4 _ _ _) indtt'') indff''
```

# Completeness for the full fragment

We need to convert an arbitrary formula `φ` to a formula `ψ` in the implication fragment
s.t. the two are provably equivalent:

```
help0 : Γ ⊢ φ ⇔ ψ → Γ ⊢ φ ⇒ ψ
help0 Γ⊢φ⇔ψ = {!   !}

help1 : Γ ⊢ φ ⇔ ψ → Γ ⊢ ψ ⇒ φ
help1 Γ⊢φ⇔ψ = {!   !}

help2 : Γ ⊢ φ ⇒ ψ → Γ ⊢ ψ ⇒ φ → Γ ⊢ φ ⇔ ψ
help2 Γ⊢φ⇒ψ Γ⊢ψ⇒φ = MP (MP E3 Γ⊢φ⇒ψ) Γ⊢ψ⇒φ

refl-⇔ : Γ ⊢ φ ⇔ φ
refl-⇔ = help2 (MP (MP A2 A1) A1) (MP (MP A2 A1) A1)

sym-⇔ : Γ ⊢ φ ⇔ ψ → Γ ⊢ ψ ⇔ φ
sym-⇔ = {!   !}

trans-⇔ : Γ ⊢ φ ⇔ ψ → Γ ⊢ ψ ⇔ ξ → Γ ⊢ φ ⇔ ξ
trans-⇔ = {!   !}

helper-⇒ : ∀ {Γ p φ ψ} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F[ p ↦ ψ ] ⇒ ξ₀ F[ p ↦ φ ] →
  Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ] →
  --------------------------------------------------------
  Γ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ⇒ ξ₁) F[ p ↦ ψ ]

helper-⇒ {Γ} {p} {φ} {ψ} ξ₀ ξ₁ ass₀ ass₁ = dt2 (dt2 goal) where

    Ξ₀ = Γ · (ξ₀ ⇒ ξ₁) F[ p ↦ φ ] · ξ₀ F[ p ↦ ψ ]

    goal = ε
        have Ξ₀ ⊢ ξ₀ F[ p ↦ ψ ]                 by Ass here
        have Ξ₀ ⊢ ξ₀ F[ p ↦ ψ ] ⇒ ξ₀ F[ p ↦ φ ] by mon2-⊢ ass₀
        have Ξ₀ ⊢ ξ₀ F[ p ↦ φ ]                 apply MP at here ,, there here
        have Ξ₀ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ]          by Ass (there here)
        have Ξ₀ ⊢ ξ₁ F[ p ↦ φ ]                 apply MP at here ,, there here
        have Ξ₀ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ] by mon2-⊢ ass₁
        have Ξ₀ ⊢ ξ₁ F[ p ↦ ψ ]                 apply MP at here ,, there here
        haveit

helper-⇔ : ∀ {Γ p φ ψ} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F[ p ↦ φ ] ⇔ ξ₀ F[ p ↦ ψ ] →
  Γ ⊢ ξ₁ F[ p ↦ φ ] ⇔ ξ₁ F[ p ↦ ψ ] →
  ------------------------------------------------
  Γ ⊢ (ξ₀ ⇔ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ⇔ ξ₁) F[ p ↦ ψ ]

helper-⇔ {Γ} {p} {φ} {ψ} ξ₀ ξ₁ ass₀ ass₁
  = dt2 (help2 goal₀ goal₁) where

  Γ₀ = Γ · (ξ₀ ⇔ ξ₁) F[ p ↦ φ ]

  goal₀ = ε
    have Γ ⊢ ξ₀ F[ p ↦ ψ ] ⇒ ξ₀ F[ p ↦ φ ]                by help1 ass₀
    have Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ]                by help0 ass₁
    have Γ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ⇒ ξ₁) F[ p ↦ ψ ]  apply helper-⇒ ξ₀ ξ₁ at there here ,, here

    have Γ₀ ⊢ (ξ₀ ⇔ ξ₁) F[ p ↦ φ ]                        by Ass here
    have Γ₀ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ]                        apply help0 at here , tt
    have Γ₀ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ⇒ ξ₁) F[ p ↦ ψ ] apply mon-⊢ at (there (there here)) , tt
    have Γ₀ ⊢ (ξ₀ ⇒ ξ₁) F[ p ↦ ψ ]                        apply MP at here ,, there here
    haveit

  goal₁ = ε
    have Γ ⊢ ξ₁ F[ p ↦ ψ ] ⇒ ξ₁ F[ p ↦ φ ]                by help1 ass₁
    have Γ ⊢ ξ₀ F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ]                by help0 ass₀
    have Γ ⊢ (ξ₁ ⇒ ξ₀) F[ p ↦ φ ] ⇒ (ξ₁ ⇒ ξ₀) F[ p ↦ ψ ]  apply helper-⇒ ξ₁ ξ₀ at there here ,, here

    have Γ₀ ⊢ (ξ₀ ⇔ ξ₁) F[ p ↦ φ ]                        by Ass here
    have Γ₀ ⊢ (ξ₁ ⇒ ξ₀) F[ p ↦ φ ]                        apply help1 at here , tt
    have Γ₀ ⊢ (ξ₁ ⇒ ξ₀) F[ p ↦ φ ] ⇒ (ξ₁ ⇒ ξ₀) F[ p ↦ ψ ] apply mon-⊢ at (there (there here)) , tt
    have Γ₀ ⊢ (ξ₁ ⇒ ξ₀) F[ p ↦ ψ ]                        apply MP at here ,, there here
    haveit

cong-∨ : ∀ {Γ p φ ψ} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ] →
  Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ] →
  ------------------------------------------------
  Γ ⊢ (ξ₀ ∨ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]

cong-∨ {Γ} {p} {φ} {ψ} ξ₀ ξ₁ ass₀ ass₁ = ε
    have Γ · ξ₀ F[ p ↦ φ ] ⊢ ξ₀ F[ p ↦ ψ ]          by dt1 ass₀
    have Γ · ξ₀ F[ p ↦ φ ] ⊢ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]   apply (MP D1) at here , tt
    have Γ ⊢ ξ₀ F[ p ↦ φ ] ⇒ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]   apply dt2 at here , tt

    have Γ · ξ₁ F[ p ↦ φ ] ⊢ ξ₁ F[ p ↦ ψ ]          by dt1 ass₁
    have Γ · ξ₁ F[ p ↦ φ ] ⊢ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]   apply (MP D2) at here , tt
    have Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]   apply dt2 at here , tt

    have Γ ⊢ (ξ₀ ∨ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ∨ ξ₁) F[ p ↦ ψ ]
      apply (MP2 D3) at there (there (there here)) ,, here
    haveit

cong-∧ : ∀ {Γ p φ ψ} ξ₀ ξ₁ →
  Γ ⊢ ξ₀ F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ] →
  Γ ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ] →
  ------------------------------------------------
  Γ ⊢ (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ∧ ξ₁) F[ p ↦ ψ ]

cong-∧ {Γ} {p} {φ} {ψ} ξ₀ ξ₁ ass₀ ass₁ = ε
      have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₀ F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ]   by mon-⊢ ass₀
      have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₀ F[ p ↦ φ ]                   by MP C1 (Ass here) 
      have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₀ F[ p ↦ ψ ]                   apply MP at there here ,, here
      have Γ ⊢ (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⇒ ξ₀ F[ p ↦ ψ ]                   apply dt2 at here , tt

      have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₁ F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ]   by mon-⊢ ass₁
      have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₁ F[ p ↦ φ ]                   by MP C2 (Ass here)
      have Γ · (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⊢ ξ₁ F[ p ↦ ψ ]                   apply MP at there here ,, here
      have Γ ⊢ (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⇒ ξ₁ F[ p ↦ ψ ]                   apply dt2 at here , tt

      have Γ ⊢ (ξ₀ ∧ ξ₁) F[ p ↦ φ ] ⇒ (ξ₀ ∧ ξ₁) F[ p ↦ ψ ]
        apply (MP2 C3) at there (there (there (there here))) ,, here
      haveit

cong-↔ : ∀ ξ p →
  Γ ⊢ φ ⇔ ψ →
  -----------------------------
  Γ ⊢ ξ F[ p ↦ φ ] ⇔ ξ F[ p ↦ ψ ]

cong-↔ ⊥ p Γ⊢φ⇔ψ = refl-⇔

cong-↔ ⊤ p Γ⊢φ⇔ψ = refl-⇔

cong-↔ (` q) p Γ⊢φ⇔ψ
  with p ≡? q
... | yes _ = Γ⊢φ⇔ψ
... | no _ = refl-⇔

cong-↔ {Γ} {φ} {ψ} (¬ ξ) p Γ⊢φ⇔ψ
  with cong-↔ ξ p Γ⊢φ⇔ψ
... | Γ⊢ξ[p↦φ]⇔ξ[p↦ψ]
  with help0 Γ⊢ξ[p↦φ]⇔ξ[p↦ψ] |
       help1 Γ⊢ξ[p↦φ]⇔ξ[p↦ψ]
... | Γ⊢ξ[p↦φ]⇒ξ[p↦ψ] | Γ⊢ξ[p↦ψ]⇒ξ[p↦φ]
  = help2 Γ⊢¬ξ[p↦φ]⇒¬ξ[p↦ψ] Γ⊢¬ξ[p↦ψ]⇒¬ξ[p↦φ] where

    Γ⊢¬ξ[p↦φ]⇒¬ξ[p↦ψ] : Γ ⊢ ¬ ξ F[ p ↦ φ ] ⇒ ¬ ξ F[ p ↦ ψ ]
    Γ⊢¬ξ[p↦φ]⇒¬ξ[p↦ψ] = MP B6 Γ⊢ξ[p↦ψ]⇒ξ[p↦φ]
    
    Γ⊢¬ξ[p↦ψ]⇒¬ξ[p↦φ] : Γ ⊢ ¬ ξ F[ p ↦ ψ ] ⇒ ¬ ξ F[ p ↦ φ ]
    Γ⊢¬ξ[p↦ψ]⇒¬ξ[p↦φ] = MP B6 Γ⊢ξ[p↦φ]⇒ξ[p↦ψ]

cong-↔ (ξ₀ ∨ ξ₁) p Γ⊢φ⇔ψ
  with cong-↔ ξ₀ p Γ⊢φ⇔ψ | cong-↔ ξ₁ p Γ⊢φ⇔ψ
... | Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
  with help0 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | help1 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] |
       help0 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ] | help1 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
... | Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] | Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ]
    | Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ] | Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ]
  = help2 (cong-∨ ξ₀ ξ₁ Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ])
          (cong-∨ ξ₀ ξ₁ Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ] Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ])

cong-↔ (ξ₀ ∧ ξ₁) p Γ⊢φ⇔ψ
  with cong-↔ ξ₀ p Γ⊢φ⇔ψ | cong-↔ ξ₁ p Γ⊢φ⇔ψ
... | Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
  with help0 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | help1 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] |
       help0 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ] | help1 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
... | Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] | Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ]
    | Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ] | Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ]
  = help2 (cong-∧ ξ₀ ξ₁ Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ])
          (cong-∧ ξ₀ ξ₁ Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ] Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ])

cong-↔ (ξ₀ ⇒ ξ₁) p Γ⊢φ⇔ψ 
  with cong-↔ ξ₀ p Γ⊢φ⇔ψ | cong-↔ ξ₁ p Γ⊢φ⇔ψ
... | Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
  with help0 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | help1 Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] |
       help0 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ] | help1 Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
... | Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] | Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ]
    | Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ] | Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ]
  = help2 (helper-⇒ ξ₀ ξ₁ Γ⊢ξ₀[p↦ψ]⇒ξ₀[p↦φ] Γ⊢ξ₁[p↦φ]⇒ξ₁[p↦ψ])
          (helper-⇒ ξ₀ ξ₁ Γ⊢ξ₀[p↦φ]⇒ξ₀[p↦ψ] Γ⊢ξ₁[p↦ψ]⇒ξ₁[p↦φ])

cong-↔ (ξ₀ ⇔ ξ₁) p Γ⊢φ⇔ψ
  with cong-↔ ξ₀ p Γ⊢φ⇔ψ | cong-↔ ξ₁ p Γ⊢φ⇔ψ
... | Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] | Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]
  = help2 (helper-⇔ ξ₀ ξ₁ Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ] Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ])
          (helper-⇔ ξ₀ ξ₁ (sym-⇔ Γ⊢ξ₀[p↦φ]⇔ξ₀[p↦ψ]) (sym-⇔ Γ⊢ξ₁[p↦φ]⇔ξ₁[p↦ψ]))

-- this is actually false;
-- turn it into an exercise
cong-alt : ∀ ξ p →
  Γ ⊢ φ ⇔ ψ →
  -------------------------------
  Γ ⊢ φ F[ p ↦ ξ ] ⇔ ψ F[ p ↦ ξ ]

cong-alt ξ p Γ⊢φ⇔ψ = {!   !}

cong2-↔ : ∀ {φ ψ φ′ ψ′} ξ p q →
  Γ ⊢ φ ⇔ ψ →
  Γ ⊢ φ′ ⇔ ψ′ →
  -------------------------------------------------------
  --Γ ⊢ ξ F[ p ↦ φ ] F[ q ↦ φ′ ] ⇔ ξ F[ p ↦ ψ ] F[ q ↦ ψ′ ]
  Γ ⊢ ξ F2[ p , q ↦ φ , φ′ ] ⇔ ξ F2[ p , q ↦ ψ , ψ′ ]

cong2-↔ {Γ} {φ} {ψ} {φ′} {ψ′} ξ p q Γ⊢φ⇔ψ Γ⊢φ′⇔ψ′ = ε
    have Γ ⊢ ξ F[ p ↦ φ ] ⇔ ξ F[ p ↦ ψ ]                          by cong-↔ ξ p Γ⊢φ⇔ψ


    have Γ ⊢ ξ F2[ p , q ↦ φ , φ′ ] ⇔ ξ F2[ p , q ↦ ψ , ψ′ ] by {!   !}
    haveit

equiv-¬ : Γ ⊢ ¬ φ ⇔ φ ⇒ ⊥
equiv-¬ = {!   !}

equiv-∨ : Γ ⊢ (φ ∨ ψ) ⇔ ((φ ⇒ ⊥) ⇒ ψ)
equiv-∨ = {!   !}

equiv-∧ : Γ ⊢ (φ ∧ ψ) ⇔ ((φ ⇒ ψ ⇒ ⊥) ⇒ ⊥)
equiv-∧ = {!   !}

equiv-⇔ : Γ ⊢ (φ ⇔ ψ) ⇔ (((φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ ⊥) ⇒ ⊥)
equiv-⇔ = {!   !}

-- notice that we need only the ψ ⇒ φ direction
convert : ∀ φ → ∃[ ψ ] Formula[⇒,⊥] ψ × ∅ ⊢ φ ⇔ ψ

convert ⊥ = _ , ⊥ , refl-⇔

convert ⊤ = _ , ` p₀ ⇒ ` p₀ , {!   !}

convert (` p) = _ , ` p , refl-⇔

convert (¬ φ)
  with convert φ
... | ψ , view-ψ , ⊢φ⇔ψ = ψ ⇒ ⊥ , view-ψ ⇒ ⊥ , (ε
  have ε ⊢ ¬ φ ⇔ (φ ⇒ ⊥)      by equiv-¬
  have ε ⊢ (φ ⇒ ⊥) ⇔ (ψ ⇒ ⊥)  by cong-↔ (` p₀ ⇒ ⊥) p₀ ⊢φ⇔ψ
  have ε ⊢ ¬ φ ⇔ (ψ ⇒ ⊥)      apply trans-⇔ at there here ,, here
  haveit)

convert (φ ∨ ψ)
  with convert φ | convert ψ
... | φ′ , view-φ′ , ⊢φ⇔φ′
    | ψ′ , view-ψ′ , ⊢ψ⇔ψ′
    = (φ′ ⇒ ⊥) ⇒ ψ′ , (view-φ′ ⇒ ⊥) ⇒ view-ψ′ , (ε
    have ε ⊢ φ ∨ ψ ⇔ ((φ ⇒ ⊥) ⇒ ψ)            by equiv-∨
    have ε ⊢ ((φ ⇒ ⊥) ⇒ ψ) ⇔ ((φ′ ⇒ ⊥) ⇒ ψ′)  by cong2-↔ ((` p₀ ⇒ ⊥) ⇒ ` p₁) p₀ p₁ ⊢φ⇔φ′ ⊢ψ⇔ψ′
    have ε ⊢ φ ∨ ψ ⇔ (φ′ ⇒ ⊥) ⇒ ψ′            apply trans-⇔ at there here ,, here
    haveit)

convert (φ ∧ ψ)
  with convert φ | convert ψ
... | φ′ , view-φ′ , ⊢φ⇔φ′
    | ψ′ , view-ψ′ , ⊢ψ⇔ψ′
    = (φ′ ⇒ ψ′ ⇒ ⊥) ⇒ ⊥ , ((view-φ′ ⇒ (view-ψ′ ⇒ ⊥)) ⇒ ⊥) , (ε
    have ε ⊢ φ ∧ ψ ⇔ (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥              by equiv-∧
    have ε ⊢ (φ ⇒ ψ ⇒ ⊥) ⇒ ⊥ ⇔ (φ′ ⇒ ψ′ ⇒ ⊥) ⇒ ⊥  by cong2-↔ ((` p₀ ⇒ ` p₁ ⇒ ⊥) ⇒ ⊥) p₀ p₁ ⊢φ⇔φ′ ⊢ψ⇔ψ′
    have ε ⊢ φ ∧ ψ ⇔ (φ′ ⇒ ψ′ ⇒ ⊥) ⇒ ⊥            apply trans-⇔ at there here ,, here
    haveit)

convert (φ ⇒ ψ)
  with convert φ | convert ψ
... | φ′ , view-φ′ , ⊢φ⇔φ′
    | ψ′ , view-ψ′ , ⊢ψ⇔ψ′
    = φ′ ⇒ ψ′ , view-φ′ ⇒ view-ψ′ , cong2-↔ (` p₀ ⇒ ` p₁) p₀ p₁ ⊢φ⇔φ′ ⊢ψ⇔ψ′


convert (φ ⇔ ψ)
  with convert φ | convert ψ
... | φ′ , view-φ′ , ⊢φ⇔φ′
    | ψ′ , view-ψ′ , ⊢ψ⇔ψ′
    = (((φ′ ⇒ ψ′) ⇒ (ψ′ ⇒ φ′) ⇒ ⊥) ⇒ ⊥) ,
      (((view-φ′ ⇒ view-ψ′) ⇒ ((view-ψ′ ⇒ view-φ′) ⇒ ⊥)) ⇒ ⊥) , (ε
    have ε ⊢ (φ ⇔ ψ) ⇔ (((φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ ⊥) ⇒ ⊥)
      by equiv-⇔
    have ε ⊢ (((φ ⇒ ψ) ⇒ (ψ ⇒ φ) ⇒ ⊥) ⇒ ⊥) ⇔ (((φ′ ⇒ ψ′) ⇒ (ψ′ ⇒ φ′) ⇒ ⊥) ⇒ ⊥)
      by cong2-↔ ((((` p₀ ⇒ ` p₁) ⇒ (` p₁ ⇒ ` p₀) ⇒ ⊥) ⇒ ⊥)) p₀ p₁ ⊢φ⇔φ′ ⊢ψ⇔ψ′
    have ε ⊢ (φ ⇔ ψ) ⇔ (((φ′ ⇒ ψ′) ⇒ (ψ′ ⇒ φ′) ⇒ ⊥) ⇒ ⊥)
      apply trans-⇔ at there here ,, here
    haveit)
```


## Weak completeness

```
weak-completeness : Formula[⇒,⊥] φ → ε ⊨ φ → ε ⊢ φ
weak-completeness {φ} viewφ ⊨φ = ε⊢φ where

  anyVal : Val
  anyVal = λ _ → tt

  have : drop n vars ^^ anyVal ⊢ φ
  have = core-lemma2 viewφ ⊨φ n anyVal refl-≤

  vars-len : length vars ≡ n
  vars-len = begin
     length vars ≡⟨⟩
     length {A = Formula} (map `_ (enumFin _)) ≡⟨ map-length `_ (enumFin _) ⟩
     length (enumFin _) ≡⟨ enumFinLen n ⟩
     n ∎

  eql : drop n vars ≡ ε
  eql = begin
    drop n vars ≡⟨ cong (λ C → drop C vars) (sym vars-len) ⟩
    drop (length vars) vars ≡⟨ drop-all vars ⟩
    ε ∎

  eql1 : drop n vars ^^ anyVal ≡ ε
  eql1 = begin
     drop n vars ^^ anyVal
       ≡⟨ cong (λ C → C ^^ anyVal) eql  ⟩
     ε ^^ anyVal
       ≡⟨⟩
     ε ∎
  
  ε⊢φ : ε ⊢ φ
  ε⊢φ = repl have (cong (λ C → C ⊢ φ) eql1)
  
```

```
weak-completeness' : ε ⊨ φ → ε ⊢ φ
weak-completeness' {φ} ⊨φ
  with convert φ
... | ψ , view-ψ , ⊢φ⇔ψ
  with help0 ⊢φ⇔ψ | help1 ⊢φ⇔ψ
... | ⊢φ⇒ψ | ⊢ψ⇒φ
  with soundness ⊢φ⇒ψ
... | ⊨φ⇒ψ 
  with modus-ponens φ ψ ⊨φ⇒ψ ⊨φ
... | ⊨ψ = ⊢φ where

  ⊢ψ : ε ⊢ ψ
  ⊢ψ = weak-completeness view-ψ ⊨ψ

  ⊢φ : ε ⊢ φ
  ⊢φ = MP ⊢ψ⇒φ ⊢ψ
```

## Strong completeness

```
completeness : ∀ φ Δ → Formula[⇒,⊥] φ → All Formula[⇒,⊥] Δ → Δ ⊨ φ → Δ ⊢ φ
completeness φ Δ viewφ viewΔ = begin→
  Δ ⊨ φ
    →⟨ longSemDT1 ⟩
  ε ⊨ Δ Imply φ
    →⟨ weak-completeness (view Δ φ viewφ viewΔ) ⟩
  ε ⊢ Δ Imply φ
    →⟨ deductionTheorem ⟩
  Δ ⊢ φ
  ∎→  where

  view : ∀ Δ φ → Formula[⇒,⊥] φ → All Formula[⇒,⊥] Δ → Formula[⇒,⊥] (Δ Imply φ)
  view ε φ viewφ viewΔ = viewφ
  view (ψ ∷ Δ) φ viewφ viewΔ = view Δ (ψ ⇒ φ) (viewψ ⇒ viewφ) (viewΔ ∘ there) where

    viewψ : Formula[⇒,⊥] ψ
    viewψ = viewΔ here
```

The following is the milestone of this chapter:

```
completeness' :
  Δ ⊨ φ →
  -----
  Δ ⊢ φ

completeness' {Δ} {φ} = begin→
  Δ ⊨ φ
    →⟨ longSemDT1 ⟩
  ε ⊨ Δ Imply φ
    →⟨ weak-completeness' ⟩
  ε ⊢ Δ Imply φ
    →⟨ deductionTheorem ⟩
  Δ ⊢ φ
  ∎→
```

