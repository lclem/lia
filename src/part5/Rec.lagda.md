---
title: "Recursion expressions 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Rec where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_; _$_) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _∸_ to _-ℕ_; _≤_ to _≤ℕ_) public
```

Syntax:

```
VarName = ℕ
FunName = ℕ

x₀ x₁ : VarName
x₀ = 0
x₁ = 1

f₀ f₁ : FunName
f₀ = 0
f₁ = 1

data Exp : Set where
  #_ : (n : ℕ) → Exp
  `_ : (x : VarName) → Exp
  _+_ _-_ _·_ : (e₀ e₁ : Exp) → Exp
  If_Then_Else_ : (e₀ e₁ e₂ : Exp) → Exp
  _$_ : (f : FunName) (e : Exp) → Exp
  Let_≔_In_ : (x : VarName) (e f : Exp) → Exp
  Rec_[_]≔_In_ : (f : FunName) (x : VarName) (e₀ e₁ : Exp) → Exp

private
  variable
    x : VarName
    f : FunName
    e e′ e₀ e₁ e₂ : Exp
    k m n n₀ n₁ : ℕ
```

```
infix 50 #_ `_
infixl 25 _+_ _-_
infixl 26 _·_
infixl 30 _$_
infixr 20 If_Then_Else_
infixr 15 Let_≔_In_ Rec_[_]≔_In_
```

Example:

```
factorial : Exp
factorial = Rec f₀ [ x₀ ]≔ If (` x₀) Then (# 1) Else ((` x₀) · f₀ $ (` x₀ - # 1)) In f₀ $ # 5
```

# Eager evaluation with dynamic binding

Eager semantics means that when evaluating an application (call) `f $ e` we must evaluate the argument `e` before passing it to `f`.
The same applies to `Let x ≔ e₀ In e₁`.

Dynamic binding means that the free numerical and functional variables appearing in `e₀` in `Rec f [ x ]≔ e₀ In e₁` are evaluated according to the environment at the time of call.
The same applies to `Let x ≔ e₀ In e₁`.

```
VarEnv = VarName → ℕ
FunEnv = FunName → (VarName × Exp)

Env = VarEnv × FunEnv

ϱ₀ : VarEnv
ϱ₀ = const 0

τ₀ : FunEnv
τ₀ = const (x₀ , # 0)

γ₀ : Env
γ₀ = ϱ₀ , τ₀

private
  variable
    γ : Env
    ϱ : VarEnv
    τ : FunEnv
```

## Natural semantics

```
infix 4 _,_⇒_
data _,_⇒_ : Exp → Env → ℕ → Set where

  ⇒-Num :
    -------------
    # n , γ ⇒ n

  ⇒-Var :
    ---------------
    ` x , (ϱ , τ) ⇒ ϱ x

  ⇒-Add :
    e₀ , γ ⇒ n₀ →
    e₁ , γ ⇒ n₁ →
    ------------------
    e₀ + e₁ , γ ⇒ n₀ +ℕ n₁

  ⇒-Sub :
    e₀ , γ ⇒ n₀ →
    e₁ , γ ⇒ n₁ →
    ------------------
    e₀ - e₁ , γ ⇒ n₀ -ℕ n₁

  ⇒-Mul :
    e₀ , γ ⇒ n₀ →
    e₁ , γ ⇒ n₁ →
    ------------------
    e₀ · e₁ , γ ⇒ n₀ ·ℕ n₁

  ⇛-App :
    e , (ϱ , τ) ⇒ m →
    let (x , e′) = τ f in
    e′ , (ϱ [ x ↦ m ] , τ) ⇒ n →
    -----------------------------
    (f $ e) , (ϱ , τ) ⇒ m

  ⇒-Let :
    e₀ , (ϱ , τ) ⇒ m →
    e₁ , (ϱ [ x ↦ m ] , τ) ⇒ n →
    -------------------------------
    Let x ≔ e₀ In e₁ , (ϱ , τ) ⇒ n

  ⇒-Rec :
    e₁ , (ϱ , τ [ f ↦ x , e₀ ]) ⇒ n →
    ------------------------------------
    Rec f [ x ]≔ e₀ In e₁ , (ϱ , τ) ⇒ n
```

## Denotational semantics

Evaluation with gas:

```
data ℕ⊥ : Set where
  ⊥ : ℕ⊥
  Just : ℕ → ℕ⊥

Just-inv : Just m ≡ Just n → m ≡ n
Just-inv refl = refl

private variable m⊥ n⊥ v₀ v₁ : ℕ⊥

lift : (ℕ → ℕ) → ℕ⊥ → ℕ⊥
lift f ⊥ = ⊥
lift f (Just x) = Just (f x)

lift2 : (ℕ → ℕ → ℕ) → ℕ⊥ → ℕ⊥ → ℕ⊥
lift2 f ⊥ _ = ⊥
lift2 f (Just _) ⊥ = ⊥
lift2 f (Just m) (Just n) = Just (f m n)

lift2-lemma : ∀ f → lift2 f v₀ v₁ ≡ Just n → ∃[ n₀ ] ∃[ n₁ ] v₀ ≡ Just n₀ × v₁ ≡ Just n₁
lift2-lemma {v₀} {v₁} f eq
  with v₀ | v₁
... | Just n₀ | Just n₁ = n₀ , n₁ , refl , refl

infixl 13 _+⊥_ _-⊥_
infixl 14 _·⊥_

_+⊥_ _-⊥_ _·⊥_ : ℕ⊥ → ℕ⊥ → ℕ⊥
_+⊥_ = lift2 _+ℕ_
_-⊥_ = lift2 _-ℕ_
_·⊥_ = lift2 _·ℕ_

ite : ℕ⊥ → ℕ⊥ → ℕ⊥ → ℕ⊥
ite ⊥ _ _ = ⊥
ite (Just 0) v₀ v₁ = v₀
ite (Just (suc _)) v₀ v₁ = v₁

⟦_⟧_#_ : Exp → Env → ℕ → ℕ⊥

⟦ # n ⟧ γ # suc _ = Just n
⟦ ` x ⟧ (ϱ , _) # suc _ = Just (ϱ x)

⟦ e₀ + e₁ ⟧ γ # suc k = ⟦ e₀ ⟧ γ # k +⊥ ⟦ e₁ ⟧ γ # k
⟦ e₀ - e₁ ⟧ γ # suc k = ⟦ e₀ ⟧ γ # k -⊥ ⟦ e₁ ⟧ γ # k
⟦ e₀ · e₁ ⟧ γ # suc k = ⟦ e₀ ⟧ γ # k ·⊥ ⟦ e₁ ⟧ γ # k

⟦ If e₀ Then e₁ Else e₂ ⟧ γ # suc k = ite (⟦ e₀ ⟧ γ # k) (⟦ e₁ ⟧ γ # k) (⟦ e₂ ⟧ γ # k)

⟦ f $ e ⟧ γ@(ϱ , τ) # suc k
  with ⟦ e ⟧ γ # k
... | ⊥ = ⊥
... | Just m = let x , e′ = τ f in ⟦ e′ ⟧ (ϱ [ x ↦ m ] , τ) # k

⟦ Let x ≔ e₀ In e₁ ⟧ γ@(ϱ , τ) # suc k
  with ⟦ e₀ ⟧ γ # k
... | ⊥ = ⊥
... | Just m = ⟦ e₁ ⟧ (ϱ [ x ↦ m ] , τ) # k

⟦ Rec f [ x ]≔ e₀ In e₁ ⟧ (ϱ , τ) # suc k = ⟦ e₁ ⟧ (ϱ , τ [ f ↦ x , e₀ ]) # k

⟦ _ ⟧ γ # 0 = ⊥
```

```
_ : ⟦ If # 0 Then # 20 · # 30 - # 1 Else # 20 ⟧ γ₀ # 10 ≡ Just 599
_ = refl

_ : ⟦ factorial ⟧ γ₀ # 1000 ≡ Just 120
_ = refl
```

## Agreement

```
-- prop-+ : ⟦ e₀ + e₁ ⟧ γ # k ≡ Just n → k ≡ suc k′
-- prop-+

agree-1 : ∀ e → ⟦ e ⟧ γ # k ≡ Just n → e , γ ⇒ n

agree-1 {k = suc k} (# n) refl = ⇒-Num

agree-1 {k = suc k} (` x) refl = ⇒-Var

agree-1 {k = suc k} (e₀ + e₁) eq
  with lift2-lemma _+ℕ_ eq
... | n₀ , n₁ , eq₀ , eq₁
  with agree-1 e₀ eq₀ |
       agree-1 e₁ eq₁
... | ind₀ | ind₁ rewrite eq₀ | eq₁ | sym (Just-inv eq) = ⇒-Add ind₀ ind₁

agree-1 (e - e₁) eq = {!   !}
agree-1 (e · e₁) eq = {!   !}

agree-1 (If e Then e₁ Else e₂) eq = {!   !}
agree-1 (f $ e) eq = {!   !}
agree-1 (Let x ≔ e In e₁) eq = {!   !}
agree-1 (Rec f [ x ]≔ e In e₁) eq = {!   !}
```