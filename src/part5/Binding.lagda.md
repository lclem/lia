---
title: "Binding 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Binding where
open import part0.index hiding (AExp; A⟦_⟧; _≈_) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _≤_ to _≤ℕ_) public
open import part5.Exp using (VarName)
open import part5.Imp using (State)

x₀ : VarName
x₀ = 0

private
  variable
    m n n₀ n₁ : ℕ
    x y : VarName
    s s′ s″ s‴ : State
```

We try to represend binding with HOAS:

```
data AExp : Set

data AExp where
  $_ : (n : ℕ) → AExp
  `_ : (x : VarName) → AExp
  _+_ : (e₀ e₁ : AExp) → AExp
  _·_ : (e₀ e₁ : AExp) → AExp
  App : AExp → AExp → AExp
  Abs : (f : VarName → AExp) → AExp

infix 50 $_ `_
infixr 30 _·_
infixl 25 _+_
--infixr 20 Let_

private
  variable
    e e₀ e₁ f : AExp
```

ide : AExp
ide = Abs λ x → ` x

```
fv : AExp → VarName *
fresh : AExp → VarName

fv ($ n) = ε
fv (` x) = [ x ]
fv (e₀ + e₁) = fv e₀ ++ fv e₁
fv (e₀ · e₁) = fv e₀ ++ fv e₁
fv (App e₀ e₁) = fv e₀ ++ fv e₁
fv (Abs f) = {!   !}
--  with 

fresh e = {!   !}
```

```
Env = VarName → ℕ

-- ⟦_⟧_ : AExp → Env → ℕ
-- ⟦ $ n ⟧ ϱ = n
-- ⟦ ` x ⟧ ϱ = ϱ x
-- ⟦ e + f ⟧ ϱ = ⟦ e ⟧ ϱ +ℕ ⟦ f ⟧ ϱ
-- ⟦ e · f ⟧ ϱ = ⟦ e ⟧ ϱ ·ℕ ⟦ f ⟧ ϱ
-- ⟦ Abs f ⟧ ϱ = {!   !} -- ⟦ f x₀ ⟧ ϱ -- ⟦ f ⟧ ϱ [ x ↦ ⟦ e ⟧ ϱ ]
-- ⟦ App e₀ e₁ ⟧ ϱ = {!   !}
```

```
-- infix 4 _,_⇒_

-- data _,_⇒_ : AExp → State → ℕ → Set

-- data _,_⇒_ where

--   ⇒-Num :
--     -----------------
--     $ n , s ⇒A n

--   ⇒-Var :
--     --------------------
--     ` x , s ⇒A s x , s

--   ⇒-Add :
--     e , s ⇒A m , s′ →
--     f , s′ ⇒A n , s″ →
--     -----------------------
--     e + f , s ⇒A m +ℕ n , s″

--   ⇒-Mul :
--     e , s ⇒A m , s′ →
--     f , s′ ⇒A n , s″ →
--     -----------------------
--     e · f , s ⇒A m ·ℕ n , s″ 

--   ⇒-Let :
--     e , s ⇒A m , s′ →
--     f , s′ [ x ↦ m ] ⇒A n , s″ →
--     ---------------------
--     Let x e f , s ⇒A n , s″

--   →-ResultIs :
--     c , s ⇒ s′ →
--     e , s′ ⇒A n , s″ →
--     -------------------------
--     c ResultIs e , s ⇒A n , s″

```