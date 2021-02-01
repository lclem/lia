---
title: "Higher-order recursion 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.HigherOrder where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_; _$_; trans-⊑; refl-⊑) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _∸_ to _-ℕ_; _≤_ to _≤ℕ_) public
```

# Syntax

## Types

```
data Type : Set where
  Int : Type
  _*_ _⟶_ : (τ₀ τ₁ : Type) → Type

private
  variable
    τ τ₀ τ₁ : Type
```

```
inj-* : Injective2 _*_
inj-* _ _ _ _ refl = refl , refl

inj-⟶ : Injective2 _⟶_
inj-⟶ _ _ _ _ refl = refl , refl
```

## Expressions

```
VarName = ℕ

x₀ x₁ f₀ f₁ : VarName
x₀ = 0
x₁ = 1
f₀ = 2
f₁ = 3

data Exp : Set where

  #_ : (n : ℕ) → Exp

  `_ : (x : VarName) → Exp

  _+_ _-_ _*_ : (e₀ e₁ : Exp) → Exp

  If_Then_Else_ : (e₀ e₁ e₂ : Exp) → Exp

  ⟨_,_⟩ : (e₀ e₁ : Exp) → Exp
  π₀_ π₁_ : (e : Exp) → Exp

  ƛ_·_ : (x : VarName) (e : Exp) → Exp
  _·_ : (e₀ e₁ : Exp) → Exp

  μ_·_ : (f : VarName) (e : Exp) → Exp

infix 50 #_ `_
infixl 25 _+_ _-_
infixl 26 _*_
infixl 30 _·_
infixr 20 If_Then_Else_
infixr 19 ⟨_,_⟩
infixr 18 π₀_ π₁_
infixr 17 ƛ_·_ μ_·_

private
  variable
    x y f : VarName
    e e′ e₀ e₁ e₂ : Exp
    k k′ k₀ k₁ m n n₀ n₁ : ℕ
```

```
--
```

Example:

```
factorial : Exp
factorial = μ f₀ · ƛ x₀ · If ` x₀ Then # 1 Else ` x₀ * ` f₀ · ` x₀ - # 1
```

# Well-typed expressions

```
TypeEnv = VarName → Type

private
  variable
    ρ : TypeEnv
```

## Operational approach

```
infix 11 _⊢_∶_
data _⊢_∶_ : TypeEnv → Exp → Type → Set where

  Var : ρ ⊢ ` x ∶ ρ x

  Int : ρ ⊢ # n ∶ Int

  Add :
    ρ ⊢ e₀ ∶ Int →
    ρ ⊢ e₁ ∶ Int →
    -----------------
    ρ ⊢ e₀ + e₁ ∶ Int

  Sub :
    ρ ⊢ e₀ ∶ Int →
    ρ ⊢ e₁ ∶ Int →
    -----------------
    ρ ⊢ e₀ - e₁ ∶ Int

  Mul :
    ρ ⊢ e₀ ∶ Int →
    ρ ⊢ e₁ ∶ Int →
    -----------------
    ρ ⊢ e₀ * e₁ ∶ Int

  Prod :
    ρ ⊢ e₀ ∶ τ₀ →
    ρ ⊢ e₁ ∶ τ₁ →
    --------------------------
    ρ ⊢ ⟨ e₀ , e₁ ⟩ ∶ τ₀ * τ₁

  Proj₀ :
    ρ ⊢ e ∶ τ₀ * τ₁ →
    -----------------
    ρ ⊢ π₀ e ∶ τ₀

  Proj₁ :
    ρ ⊢ e ∶ τ₀ * τ₁ →
    -----------------
    ρ ⊢ π₁ e ∶ τ₁

  Abs :
    ρ ⊢ e ∶ τ →
    ----------------------
    ρ ⊢ ƛ x · e ∶ ρ x ⟶ τ₀

  App :
    ρ ⊢ e₀ ∶ τ₀ ⟶ τ₁ →
    ρ ⊢ e₁ ∶ τ₀ →
    ------------------
    ρ ⊢ e₀ · e₁ ∶ τ₁

```

## Denotational approach

```
data Type⊥ : Set where
  ⊥ : Type⊥
  ⌊_⌋ : Type → Type⊥

lift : (Type → Type) → Type⊥ → Type⊥
lift f ⊥ = ⊥
lift f ⌊ x ⌋ = ⌊ f x ⌋

lift2 : (Type → Type → Type) → Type⊥ → Type⊥ → Type⊥
lift2 f ⊥ _ = ⊥
lift2 f _ ⊥ = ⊥
lift2 f ⌊ x ⌋ ⌊ y ⌋ = ⌊ f x y ⌋

lift⊥ : (Type → Type⊥) → Type⊥ → Type⊥
lift⊥ f ⊥ = ⊥
lift⊥ f ⌊ x ⌋ = f x

lift2⊥ : (Type → Type → Type⊥) → Type⊥ → Type⊥ → Type⊥
lift2⊥ f ⊥ _ = ⊥
lift2⊥ f _ ⊥ = ⊥
lift2⊥ f ⌊ x ⌋ ⌊ y ⌋ = f x y

lift3⊥ : (Type → Type → Type → Type⊥) → Type⊥ → Type⊥ → Type⊥ → Type⊥
lift3⊥ f ⊥ _ _ = ⊥
lift3⊥ f _ ⊥ _ = ⊥
lift3⊥ f _ _ ⊥ = ⊥
lift3⊥ f ⌊ x ⌋ ⌊ y ⌋ ⌊ z ⌋ = f x y z
```

Types have a decidable equality:

```
_≟T_ : Decidable2 (_≡_ {A = Type})
Int ≟T Int = yes refl
Int ≟T (_ * _) = no λ ()
Int ≟T (_ ⟶ _) = no λ ()
(_ * _) ≟T Int = no λ ()
(a₀ * a₁) ≟T (b₀ * b₁) = dec-iso ((a₀ ≟T b₀) ×? (a₁ ≟T b₁)) (cong2′ _*_ , cong2-inv inj-*)
(_ * _) ≟T (_ ⟶ _) = no λ ()
(_ ⟶ _) ≟T Int = no λ ()
(_ ⟶ _) ≟T (_ * _) = no λ ()
(a₀ ⟶ a₁) ≟T (b₀ ⟶ b₁) = dec-iso ((a₀ ≟T b₀) ×? (a₁ ≟T b₁)) (cong2′ _⟶_ , cong2-inv inj-⟶)

instance
  eqT : Eq Type
  _≡?_ {{eqT}} = _≟T_
```

```
type-Int2 : Type → Type → Type⊥
type-Int2 Int Int = ⌊ Int ⌋
type-Int2 _ _ = ⊥

type-Int3 : Type → Type → Type → Type⊥
type-Int3 Int Int Int = ⌊ Int ⌋
type-Int3 _ _ _ = ⊥

type-Prod : Type → Type → Type
type-Prod τ₀ τ₁ = τ₀ * τ₁

type-Proj₀ : Type → Type⊥
type-Proj₀ (τ₀ * τ₁) = ⌊ τ₀ ⌋
type-Proj₀ _ = ⊥

type-Proj₁ : Type → Type⊥
type-Proj₁ (τ₀ * τ₁) = ⌊ τ₁ ⌋
type-Proj₁ _ = ⊥

type-Abs : Type → Type → Type
type-Abs τ₀ τ₁ = τ₀ ⟶ τ₁

type-App : Type → Type → Type⊥
type-App (τ₀ ⟶ τ₁) τ₂
  with τ₂ ≡? τ₀
... | yes _ = ⌊ τ₁ ⌋
... | no _ = ⊥
type-App _ _ = ⊥

type-Rec : Type → Type → Type⊥
type-Rec τ@(τ₀ ⟶ τ₁) τ′
  with τ′ ≡? τ
... | yes refl = ⌊ τ ⌋
... | no _ = ⊥
type-Rec _ _ = ⊥
```

```
infix 11 T⟦_⟧_
T⟦_⟧_ : Exp → TypeEnv → Type⊥

T⟦ # n ⟧ ρ = ⌊ Int ⌋

T⟦ ` x ⟧ ρ = ⌊ ρ x ⌋

T⟦ e₀ + e₁ ⟧ ρ = lift2⊥ type-Int2 (T⟦ e₀ ⟧ ρ) (T⟦ e₁ ⟧ ρ)
T⟦ e₀ - e₁ ⟧ ρ = lift2⊥ type-Int2 (T⟦ e₀ ⟧ ρ) (T⟦ e₁ ⟧ ρ)
T⟦ e₀ * e₁ ⟧ ρ = lift2⊥ type-Int2 (T⟦ e₀ ⟧ ρ) (T⟦ e₁ ⟧ ρ)

T⟦ If e₀ Then e₁ Else e₂ ⟧ ρ = lift3⊥ type-Int3 (T⟦ e₀ ⟧ ρ) (T⟦ e₁ ⟧ ρ) (T⟦ e₂ ⟧ ρ)

T⟦ ⟨ e₀ , e₁ ⟩ ⟧ ρ = lift2 type-Prod (T⟦ e₀ ⟧ ρ) (T⟦ e₁ ⟧ ρ)

T⟦ π₀ e ⟧ ρ = lift⊥ type-Proj₀ (T⟦ e ⟧ ρ)
T⟦ π₁ e ⟧ ρ = lift⊥ type-Proj₁ (T⟦ e ⟧ ρ)

T⟦ ƛ x · e ⟧ ρ = lift (type-Abs (ρ x)) (T⟦ e ⟧ ρ)
T⟦ e₀ · e₁ ⟧ ρ = lift2⊥ type-App (T⟦ e₀ ⟧ ρ) (T⟦ e₁ ⟧ ρ)

T⟦ μ f · e ⟧ ρ = lift⊥ (type-Rec (ρ f)) (T⟦ e ⟧ ρ)
```

## Agreement

# Eager evaluation with dynamic binding

```
--
```

# Eager evaluation with static binding

# Lazy evaluation with dynamic binding

# Lazy evaluation with static binding
