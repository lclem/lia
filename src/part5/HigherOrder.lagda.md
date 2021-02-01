---
title: "Higher-order recursion 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.HigherOrder where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_; _$_; trans-⊑; refl-⊑) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _∸_ to _-ℕ_; _≤_ to _≤ℕ_) public
open import part5.Maybe
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


We essentially have a λY-calculus (simply typed lambda calculus with fixpoints) with products with an ℕ base type.

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

Example:

```
-- factorial : Exp
-- factorial = μ f₀ · ƛ x₀ · (If (` x₀) Then (# 1) Else ((` x₀) * ((` f₀) · (` x₀ - (# 1)))))
```

Free variables:

```
∅ : VarName *
∅ = ε

fv : Exp → VarName *
fv (# n) = ∅
fv (` x) = [ x ]
fv (e₀ + e₁) = fv e₀ ++ fv e₁
fv (e₀ - e₁) = fv e₀ ++ fv e₁
fv (e₀ * e₁) = fv e₀ ++ fv e₁
fv (If e₀ Then e₁ Else e₂) = fv e₀ ++ fv e₁ ++ fv e₂
fv ⟨ e₀ , e₁ ⟩ = fv e₀ ++ fv e₁
fv (π₀ e) = fv e
fv (π₁ e) = fv e
fv (ƛ x · e) = remove x (fv e)
fv (e₀ · e₁) = fv e₀ ++ fv e₁
fv (μ f · e) = fv e
```

Closed expressions:

```
Closed : Exp → Set
Closed e = fv e ≡ ∅
```

# Well-typed expressions

```
TypeEnv = VarName → Type
```

Throughout the section,
we assume for simplicity a fixed, global typing environment.

```
postulate ρ : TypeEnv
```


## Operational approach

```
infix 11 _∶_
data _∶_ : Exp → Type → Set where

  Var : ` x ∶ ρ x

  Int : # n ∶ Int

  Add :
    e₀ ∶ Int →
    e₁ ∶ Int →
    -----------------
    e₀ + e₁ ∶ Int

  Sub :
    e₀ ∶ Int →
    e₁ ∶ Int →
    -----------------
    e₀ - e₁ ∶ Int

  Mul :
    e₀ ∶ Int →
    e₁ ∶ Int →
    -----------------
    e₀ * e₁ ∶ Int

  ITE :
    e₀ ∶ Int →
    e₁ ∶ τ →
    e₂ ∶ τ →
    --------------------------
    If e₀ Then e₁ Else e₂ ∶ τ

  Prod :
    e₀ ∶ τ₀ →
    e₁ ∶ τ₁ →
    --------------------------
    ⟨ e₀ , e₁ ⟩ ∶ τ₀ * τ₁

  Proj₀ :
    e ∶ τ₀ * τ₁ →
    -----------------
    π₀ e ∶ τ₀

  Proj₁ :
    e ∶ τ₀ * τ₁ →
    -----------------
    π₁ e ∶ τ₁

  Abs :
    e ∶ τ →
    -------------------
    ƛ x · e ∶ ρ x ⟶ τ

  App :
    e₀ ∶ τ₀ ⟶ τ₁ →
    e₁ ∶ τ₀ →
    ------------------
    e₀ · e₁ ∶ τ₁

  Fix :
    ` x ∶ τ →
    e ∶ τ →
    -----------
    μ x · e ∶ τ
```

One could prove that a terms gets at most one type (determinism)
and that moreover this type can be computed.
%
One could moreover prove that typing is decidable,
in fact we can do even better.
%
The following section describes a denotational approach to typing,
and one could prove that it produces exactly the unique type defined in this section (if it exists).

Inversion rules:

```
Prod-inv :
  ⟨ e₀ , e₁ ⟩ ∶ τ₀ * τ₁ →
  -----------------------
  e₀ ∶ τ₀ × e₁ ∶ τ₁

Prod-inv (Prod δ₀ δ₁) = δ₀ , δ₁

Abs-inv :
    ƛ x · e ∶ τ₀ ⟶ τ₁ →
    -------------------
    τ₀ ≡ ρ x × e ∶ τ₁

Abs-inv (Abs δ) = refl , δ
```

## Denotational approach

```
Type⊥ = Maybe Type
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

T⟦ ⟨ e₀ , e₁ ⟩ ⟧ ρ = lift2 _*_ (T⟦ e₀ ⟧ ρ) (T⟦ e₁ ⟧ ρ)

T⟦ π₀ e ⟧ ρ = lift⊥ type-Proj₀ (T⟦ e ⟧ ρ)
T⟦ π₁ e ⟧ ρ = lift⊥ type-Proj₁ (T⟦ e ⟧ ρ)

T⟦ ƛ x · e ⟧ ρ = lift (type-Abs (ρ x)) (T⟦ e ⟧ ρ)
T⟦ e₀ · e₁ ⟧ ρ = lift2⊥ type-App (T⟦ e₀ ⟧ ρ) (T⟦ e₁ ⟧ ρ)

T⟦ μ f · e ⟧ ρ = lift⊥ (type-Rec (ρ f)) (T⟦ e ⟧ ρ)
```

## Agreement

TODO














# Eager evaluation with dynamic binding

## Values

Canonical expressions describe what it means to be a value.
In the case of eager evaluation,
canonical forms are numerals and well-formed abstractions.
Moreover, pairs of canonical expressions are again canonical.

Notice that we allow canonical expressions to have free variables.
These free variables are interpreted according to dynamic binding.

```
infix 10 Canonical_∶_
data Canonical_∶_ : Exp → Type → Set where
  Int : Canonical # n ∶ Int
  Abs : {- Closed (ƛ x · e) → -} ƛ x · e ∶ τ₀ ⟶ τ₁ → Canonical ƛ x · e ∶ τ₀ ⟶ τ₁
  Prod : Canonical e₀ ∶ τ₀ → Canonical e₁ ∶ τ₁ → Canonical ⟨ e₀ , e₁ ⟩ ∶ τ₀ * τ₁
```

Notice that `Canonical e ∶ τ` implies `e ∶ τ`,
i.e., `e`  has type `τ` under environment `ρ`.

```
canonical→wf : Canonical e ∶ τ → e ∶ τ
canonical→wf Int = Int
canonical→wf (Prod c₀ c₁)
  with canonical→wf c₀ |
       canonical→wf c₁
... | ρ₀⊢e₀∶τ₀ | ρ₁⊢e₁∶τ₁ = Prod ρ₀⊢e₀∶τ₀ ρ₁⊢e₁∶τ₁
canonical→wf (Abs ρ⊢ƛx·e∶τ₀⟶τ₁) = ρ⊢ƛx·e∶τ₀⟶τ₁
```

There are several ways to evaluate a higher-order expression of the form `(ƛ x · e₀) · e₁`.
One way is to syntactically replace every free occurrence of `x` in `e₀` by `e₁`.
Since `e₁` may contain free variables in general,
this is problematic since every occurrence of a free variable of `e₁` must remain free after the substitution.
This can be achieved in a number of different ways:

1) we could demand that `e₁` is closed, i.e., it does not have free variables.
2) we could rename `x` to be a fresh variable.
3) we could delay the substitution up to until the point when it is necessary.

We chose the third approach.
Here enter *closures*.
...

## Big-steps operational semantics

Note that there are no types and no closures in the rules below.

```
--Value : Type → Set
--Value τ = ∃[ e ] Canonical e ∶ τ
-- Env = (x : VarName) → Value (ρ x)
Env = VarName → Exp

private
  variable
    ϱ : Env
    -- v : ∀ {τ} → Value τ
    u u₀ u₁ v v₀ v₁ : Exp
```

```
infix 10 _⊢_⇒_
data _⊢_⇒_ : Env → Exp → Exp → Set where

  Int : ϱ ⊢ # n ⇒ # n

--  Var : ϱ ⊢ ` x ⇒ let e , _ = ϱ x in e
  Var : ϱ ⊢ ` x ⇒ ϱ x

  Add : ϱ ⊢ e₀ ⇒ # n₀ →
        ϱ ⊢ e₁ ⇒ # n₁ →
        --------------------------
        ϱ ⊢ e₀ + e₁ ⇒ # (n₀ +ℕ n₁)

  Sub : ϱ ⊢ e₀ ⇒ # n₀ →
        ϱ ⊢ e₁ ⇒ # n₁ →
        --------------------------
        ϱ ⊢ e₀ - e₁ ⇒ # (n₀ -ℕ n₁)

  Mul : ϱ ⊢ e₀ ⇒ # n₀ →
        ϱ ⊢ e₁ ⇒ # n₁ →
        --------------------------
        ϱ ⊢ e₀ * e₁ ⇒ # (n₀ ·ℕ n₁)

  ITE-0 : ϱ ⊢ e₀ ⇒ # 0 →
          ϱ ⊢ e₁ ⇒ v →
          -------------------------------
          ϱ ⊢ If e₀ Then e₁ Else e₂ ⇒ v

  ITE-suc : ϱ ⊢ e₀ ⇒ # suc m →
            ϱ ⊢ e₂ ⇒ v →
            -------------------------------
            ϱ ⊢ If e₀ Then e₁ Else e₂ ⇒ v

  Prod : ϱ ⊢ e₀ ⇒ v₀ →
         ϱ ⊢ e₁ ⇒ v₁ →
         -----------------------------
         ϱ ⊢ ⟨ e₀ , e₁ ⟩ ⇒ ⟨ v₀ , v₁ ⟩

  Proj₀ : ϱ ⊢ e ⇒ ⟨ v₀ , v₁ ⟩ →
          ---------------------
          ϱ ⊢ π₀ e ⇒ v₀

  Proj₁ : ϱ ⊢ e ⇒ ⟨ v₀ , v₁ ⟩ →
          ---------------------
          ϱ ⊢ π₁ e ⇒ v₁

  Abs : ---------------------
        ϱ ⊢ ƛ x · e ⇒ ƛ x · e

  App : ϱ ⊢ e₀ ⇒ ƛ x · e →
        ϱ ⊢ e₁ ⇒ v₁ →
        ϱ [ x ↦ v₁ ] ⊢ e ⇒ v →
        ----------------------
        ϱ ⊢ e₀ · e₁ ⇒ v

  Fix : ϱ ⊢ e ⇒ ƛ y · e′ →
        ϱ [ x ↦ μ x · ƛ y · e′ ] ⊢ e ⇒ v →
        ----------------------------------
        ϱ ⊢ μ x · e ⇒ v
```

TODO: Illustrate the dynamic binding aspect.

### Deterministic values

```
det : ϱ ⊢ e ⇒ u →
      ϱ ⊢ e ⇒ v →
      -----------
      u ≡ v

det δ σ = {!   !}
```

### Type preservation

```
Consistent_ : Env → Set
Consistent ϱ = ∀ x → ϱ x ∶ ρ x

Consistent-preservation :
  Consistent ϱ →
  e ∶ ρ x →
  ----------------------
  Consistent ϱ [ x ↦ e ]

Consistent-preservation cn δ = {!   !}

preservation :
  e ∶ τ →
  ϱ ⊢ e ⇒ v →
  Consistent ϱ →
  ------------
  v ∶ τ

preservation Int Int _ = Int
preservation {` x} Var Var cn = cn x
preservation (Add δ δ₁) (Add σ σ₁) cn = Int
preservation (Sub δ δ₁) (Sub σ σ₁) cn = Int
preservation (Mul δ δ₁) (Mul σ σ₁) cn = Int
preservation (ITE δ₀ δ₁ δ₂) (ITE-0 σ₀ σ₁) cn = preservation δ₁ σ₁ cn
preservation (ITE δ₀ δ₁ δ₂) (ITE-suc σ₀ σ₂) cn = preservation δ₂ σ₂ cn
preservation (Prod δ₀ δ₁) (Prod σ₀ σ₁) cn = Prod (preservation δ₀ σ₀ cn) (preservation δ₁ σ₁ cn)
preservation (Proj₀ δ) (Proj₀ σ) cn = let r , _ = Prod-inv (preservation δ σ cn) in r
preservation (Proj₁ δ) (Proj₁ σ) cn = let _ , r = Prod-inv (preservation δ σ cn) in r
preservation (Abs δ) Abs cn = Abs δ
preservation (App δ₀ δ₁) (App {x = x} σ₀ σ₁ σ₂) cn
  with preservation δ₀ σ₀ cn |
       preservation δ₁ σ₁ cn
... | ind₀ | ind₁
  with Abs-inv ind₀
... | refl , ind′ 
  with Consistent-preservation cn ind₁
... | cn′ = preservation ind′ σ₂ cn′
-- similar as Abs + App
preservation (Fix δ₀ δ₁) (Fix σ₀ σ₁) cn = {!  !}
```

## Denotational semantics

Evaluation with gas.

You actually need a Krivine machine!

```
Exp⊥ = Maybe Exp

⟦_⟧_#_ : Exp → Env → ℕ → Exp⊥

⟦ e ⟧ ϱ # 0 = ⊥

⟦ # m ⟧ ϱ # suc n = ⌊ # m ⌋
⟦ ` x ⟧ ϱ # suc n = ⌊ ϱ x ⌋

⟦ e₀ + e₁ ⟧ ϱ # suc n
  with ⟦ e₀ ⟧ ϱ # n | ⟦ e₁ ⟧ ϱ # n
... | ⌊ # n₀ ⌋ | ⌊ # n₁ ⌋ = ⌊ # (n₀ +ℕ n₁) ⌋
... | _ | _ = ⊥ -- this is catching many cases

⟦ e₀ - e₁ ⟧ ϱ # suc n
  with ⟦ e₀ ⟧ ϱ # n | ⟦ e₁ ⟧ ϱ # n
... | ⌊ # n₀ ⌋ | ⌊ # n₁ ⌋ = ⌊ # (n₀ -ℕ n₁) ⌋
... | _ | _ = ⊥ -- this is catching many cases

⟦ e₀ * e₁ ⟧ ϱ # suc n
  with ⟦ e₀ ⟧ ϱ # n | ⟦ e₁ ⟧ ϱ # n
... | ⌊ # n₀ ⌋ | ⌊ # n₁ ⌋ = ⌊ # (n₀ ·ℕ n₁) ⌋
... | _ | _ = ⊥ -- this is catching many cases

⟦ If e₀ Then e₁ Else e₂ ⟧ ϱ # suc n
  with ⟦ e₀ ⟧ ϱ # n
... | ⌊ # 0 ⌋ = ⟦ e₁ ⟧ ϱ # n
... | ⌊ # suc _ ⌋ = ⟦ e₂ ⟧ ϱ # n
... | _ = ⊥ -- this is catching many cases

⟦ ⟨ e₀ , e₁ ⟩ ⟧ ϱ # suc n
  with ⟦ e₀ ⟧ ϱ # n | ⟦ e₁ ⟧ ϱ # n
... | ⌊ v₀ ⌋ | ⌊ v₁ ⌋ = ⌊ ⟨ v₀ , v₁ ⟩ ⌋
... | _ | _ = ⊥ -- this is catching many cases

⟦ π₀ e ⟧ ϱ # suc n
  with ⟦ e ⟧ ϱ # n
... | ⌊ ⟨ v , _ ⟩ ⌋ = ⌊ v ⌋
... | _ = ⊥ -- this is catching many cases

⟦ π₁ e ⟧ ϱ # suc n
  with ⟦ e ⟧ ϱ # n
... | ⌊ ⟨ _ , v ⟩ ⌋ = ⌊ v ⌋
... | _ = ⊥ -- this is catching many cases

⟦ ƛ x · e ⟧ ϱ # suc n = ⌊ ƛ x · e ⌋

⟦ e₀ · e₁ ⟧ ϱ # suc n
  with ⟦ e₀ ⟧ ϱ # n | ⟦ e₁ ⟧ ϱ # n
... | ⌊ ƛ x · e ⌋ | ⌊ v ⌋ = ⟦ e ⟧ ϱ [ x ↦ v ] # n
... | _ | _ = ⊥ -- this is catching many cases

⟦ μ x · e ⟧ ϱ # suc n
  with ⟦ e ⟧ ϱ # n
... | ⌊ ƛ y · e′ ⌋ = ⟦ ƛ y · e′ ⟧ (ϱ [ x ↦ ƛ y · e′ ]) # n
... | _ = ⊥ -- this is catching many cases
```

Example:

```
ϱ₀ : Env
ϱ₀ 0 = # 10
ϱ₀ 1 = # 11
ϱ₀ 2 = ƛ x₀ · (` x₀ + # 111) -- f₀
ϱ₀ 3 = ƛ x₀ · ` x₀ + # 2
ϱ₀ (suc (suc (suc (suc _)))) = # 0

-- _ : ⟦ ` f₀ ⟧ ϱ₀ # 100 ≡ ⌊ ƛ x₀ · ` x₀ ⌋
-- _ = refl

-- _ : ⟦ ` f₁ · ` x₁ ⟧ ϱ₀ # 100 ≡ ⌊ # 13 ⌋
-- _ = refl

-- test : Exp
-- test = ƛ x₀ · If ` x₀ Then # 1 Else # 2

-- _ : ⟦ test · # 0 ⟧ ϱ₀ # 4 ≡ ⌊ # 1 ⌋
-- _ = refl

-- _ : ⟦ test · # 1 ⟧ ϱ₀ # 4 ≡ ⌊ # 2 ⌋
-- _ = refl

factorial factorialBody : Exp
factorialBody = ƛ x₀ · (If (` x₀) Then (# 1) Else (` x₀ * ((` f₀) · ((` x₀) - (# 1)))))
factorial = μ f₀ · factorialBody

_ : ⟦ factorial ⟧ ϱ₀ # 2 ≡ ⌊ factorialBody ⌋
_ = refl

_ : ⟦ factorial · # 0 ⟧ ϱ₀ # 3 ≡ ⌊ # 1 ⌋
_ = refl

ϱ₁ = ϱ₀ [ f₀ ↦ factorialBody ]

_ : ⟦ ` f₀ · # 1 ⟧ ϱ₁ # 100 ≡ ⌊ # 1 ⌋
_ = refl

_ : ⟦ ` f₀ · # 2 ⟧ ϱ₁ # 100 ≡ ⌊ # 2 ⌋
_ = refl

_ : ⟦ ` f₀ · # 5 ⟧ ϱ₁ # 100 ≡ ⌊ # 120 ⌋
_ = refl

_ : ⟦ factorial · # 5 ⟧ ϱ₁ # 100 ≡ ⌊ # 120 ⌋
_ = refl

_ : ⟦ factorialBody ⟧ ϱ₀ # 100 ≡ ⌊ factorialBody ⌋
_ = refl

_ : ⟦ factorialBody ⟧ ϱ₁ # 100 ≡ ⌊ factorialBody ⌋
_ = refl


_ : ⟦ factorialBody · # 1 ⟧ ϱ₁ # 100 ≡ ⌊ # 1 ⌋
_ = refl

_ : ⟦ factorial · # 1 ⟧ ϱ₁ # 100 ≡ ⌊ # 1 ⌋
_ = refl

_ : ⟦ factorialBody · # 0 ⟧ ϱ₀ # 100 ≡ ⌊ # 1 ⌋
_ = refl

_ : ⟦ factorial · # 1 ⟧ ϱ₀ # 100 ≡ {! ⟦ (μ f₀ · factorialBody) · # 1 ⟧ ϱ₀ # 100 !} -- ⌊ # 1 ⌋
_ = refl

-- _ : ⟦ factorial · # 2 ⟧ ϱ₀ # 3 ≡ ⌊ # 1 ⌋
-- _ = refl

```


```
-- not enough gas
_ : ⟦ factorial · # 5 ⟧ ϱ₀ # 5 ≡ ⊥
_ = refl



```

## Agreement of the operational and denotational semantics

# Eager evaluation with static binding

# Lazy evaluation with dynamic binding

# Lazy evaluation with static binding
