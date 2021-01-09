---
title: "Arithmetic expressions with division 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Exp2 where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _≤_ to _≤ℕ_) public
open import Data.Nat.DivMod renaming (_/_ to _/ℕ_)
```

# Arithmetic expressions with division

```
VarName = ℕ

x₀ x₁ : VarName
x₀ = 0
x₁ = 1

data AExp : Set where
  Num : (n : ℕ) → AExp
  Var : (x : VarName) → AExp
  Add : (e f : AExp) → AExp
  Mul : (e f : AExp) → AExp
  Div : (e f : AExp) → AExp
  Let : (x : VarName) (e f : AExp) → AExp

private
  variable
    e e′ f f′ g : AExp
    m n : ℕ
```

```
pattern $_ n = Num n
pattern `_ x = Var x
pattern _+_ x y = Add x y
pattern _·_ x y = Mul x y
pattern _/_ x y = Div x y
pattern Let_≔_In_ x e f = Let x e f

infix 50 $_ `_
infixl 30 _·_ _/_
infixl 25 _+_
infixr 20 Let_≔_In_
```

# Eager semantics

Since division by zero can occur,
not every expression has a value.
To model this, we construct a new domain by adding `⊥`.
(An alternative way would be by modelling evaluation as a partial function,
but this is not possible since Agda's functions are total.)

```
data ℕ⊥ : Set where
  ⊥ : ℕ⊥
  Just : ℕ → ℕ⊥

private variable m⊥ n⊥ : ℕ⊥

lift : (ℕ → ℕ) → ℕ⊥ → ℕ⊥
lift f ⊥ = ⊥
lift f (Just x) = Just (f x)

lift2 : (ℕ → ℕ → ℕ) → ℕ⊥ → ℕ⊥ → ℕ⊥
lift2 f ⊥ _ = ⊥
lift2 f _ ⊥ = ⊥
lift2 f (Just m) (Just n) = Just (f m n)

Envᵉ = VarName → ℕ

ϱ₀ : Envᵉ
ϱ₀ _ = 0
```

```
infixl 13 _+⊥_
infixl 14 _·⊥_

_+⊥_ _·⊥_ : ℕ⊥ → ℕ⊥ → ℕ⊥
_+⊥_ = lift2 _+ℕ_
_·⊥_ = lift2 _·ℕ_
```

```
infix 15 ⟦_⟧ᵉ_
⟦_⟧ᵉ_ : AExp → Envᵉ → ℕ⊥

⟦ $ n ⟧ᵉ ϱ = Just n
⟦ ` x ⟧ᵉ ϱ = Just (ϱ x)
⟦ e + f ⟧ᵉ ϱ = ⟦ e ⟧ᵉ ϱ +⊥ ⟦ f ⟧ᵉ ϱ
⟦ e · f ⟧ᵉ ϱ = ⟦ e ⟧ᵉ ϱ ·⊥ ⟦ f ⟧ᵉ ϱ

⟦ e / f ⟧ᵉ ϱ
  with ⟦ e ⟧ᵉ ϱ
... | ⊥ = ⊥
... | Just m
  with ⟦ f ⟧ᵉ ϱ
... | ⊥ = ⊥
... | Just 0 = ⊥
... | Just (suc n) = Just (m /ℕ suc n)

⟦ Let x ≔ e In f ⟧ᵉ ϱ
  with ⟦ e ⟧ᵉ ϱ
... | ⊥ = ⊥ 
... | Just m = ⟦ f ⟧ᵉ ϱ [ x ↦ m ]
```

Examples:

```
_ : ⟦ Let x₀ ≔ $ 3 In $ 18 / ` x₀ ⟧ᵉ ϱ₀ ≡ Just 6
_ = refl

_ : ⟦ Let x₀ ≔ $ 0 In $ 18 / ` x₀ ⟧ᵉ ϱ₀ ≡ ⊥
_ = refl
```

# Lazy semantics

```
Envˡ = VarName → ℕ⊥

infix 15 ⟦_⟧ˡ_
⟦_⟧ˡ_ : AExp → Envˡ → ℕ⊥

⟦ $ n ⟧ˡ ϱ = Just n
⟦ ` x ⟧ˡ ϱ = ϱ x
⟦ e + f ⟧ˡ ϱ = ⟦ e ⟧ˡ ϱ +⊥ ⟦ f ⟧ˡ ϱ
⟦ e · f ⟧ˡ ϱ = ⟦ e ⟧ˡ ϱ ·⊥ ⟦ f ⟧ˡ ϱ

⟦ e / f ⟧ˡ ϱ
  with ⟦ e ⟧ˡ ϱ
... | ⊥ = ⊥
... | Just m
  with ⟦ f ⟧ˡ ϱ
... | ⊥ = ⊥
... | Just 0 = ⊥
... | Just (suc n) = Just (m /ℕ suc n)

⟦ Let x ≔ e In f ⟧ˡ ϱ = ⟦ f ⟧ˡ ϱ [ x ↦ ⟦ e ⟧ˡ ϱ ]
```

The lazy semantics can return a value while the eager semantics is undefined:

```
-- TODO
```

We show that the lazy semantics is at least as defined as the eager one,
and they agree when they are both defined.

```
infix 5 _⊑_
data _⊑_ : ℕ⊥ → ℕ⊥ → Set where
  ⊥ : ⊥ ⊑ m⊥
  Just : Just m ⊑ Just m

⊑-Just : Just m ⊑ n⊥ → n⊥ ≡ Just m
⊑-Just Just = refl

update-Just : ∀ (ϱ : Envᵉ) (x : VarName) (m : ℕ) → update {B = const ℕ⊥} (Just ∘ ϱ) x (Just m) ≡ Just ∘ update ϱ x m
update-Just ϱ x m = sym (update-∘ ϱ Just x m)

mon-lift2 : ∀ {m₀ n₀ m₁ n₁} (f : ℕ → ℕ → ℕ) →
  m₀ ⊑ m₁ →
  n₀ ⊑ n₁ →
  -----------------------------
  lift2 f m₀ n₀ ⊑ lift2 f m₁ n₁
  
mon-lift2 f ⊥ ⊥ = ⊥
mon-lift2 f ⊥ Just = ⊥
mon-lift2 f Just ⊥ = ⊥
mon-lift2 f Just Just = Just
```

```
approx : ∀ ϱ e → ⟦ e ⟧ᵉ ϱ ⊑ ⟦ e ⟧ˡ (Just ∘ ϱ)

approx ϱ ($ n) = Just

approx ϱ (` x) = Just

approx ϱ (e + f) with approx ϱ e | approx ϱ f
... | ind-e | ind-f = mon-lift2 _ ind-e ind-f

approx ϱ (e · f) with approx ϱ e | approx ϱ f
... | ind-e | ind-f = mon-lift2 _ ind-e ind-f

approx ϱ (e / f)
  with inspect (⟦ e ⟧ᵉ ϱ)
... | it ⊥ eq-e rewrite eq-e = ⊥
... | it (Just m) eq-e rewrite eq-e
  with inspect (⟦ f ⟧ᵉ ϱ)
... | it ⊥ eq-f rewrite eq-f = ⊥
... | it (Just 0) eq-f rewrite eq-f = ⊥
... | it (Just (suc n)) eq-f
  with approx ϱ e | approx ϱ f
... | ind-e | ind-f
  rewrite eq-e | eq-f | ⊑-Just ind-e | ⊑-Just ind-f = Just

approx ϱ (Let x ≔ e In f)
  with inspect (⟦ e ⟧ᵉ ϱ)
... | it ⊥ eq-e rewrite eq-e = ⊥
... | it (Just m) eq-e
  with approx ϱ e
... | ind-e
  rewrite eq-e
  with ⊑-Just ind-e
... | eq-e-l rewrite eq-e-l
  with inspect (⟦ f ⟧ᵉ ϱ [ x ↦ m ])
... | it ⊥ eq-f rewrite eq-f = ⊥
... | it (Just n) eq-f
  with approx (ϱ [ x ↦ m ]) f
... | ind-f
  rewrite eq-f
  with ⊑-Just ind-f
... | eq-f-l
  rewrite update-Just ϱ x m | eq-f-l = Just
```