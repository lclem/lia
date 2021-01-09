---
title: "Imperative programs 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Extentions where
open import part0.index hiding (AExp; A⟦_⟧; _≈_) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _≤_ to _≤ℕ_) public
open import part5.Exp using (VarName)
open import part5.Imp using (State)

private
  variable
    m n n₀ n₁ : ℕ
    x y : VarName
    s s′ s″ s‴ : State
```

# Side effects

```
module SideEffects where
```

## Arithmetic expressions

```
data AExp : Set
data Cmd : Set

data AExp where
  Num : (n : ℕ) → AExp
  Var : (x : VarName) → AExp
  Add : (e f : AExp) → AExp
  Mul : (e f : AExp) → AExp
  Let : (x : VarName) (e f : AExp) → AExp
  _ResultIs_ : Cmd → AExp → AExp

pattern $_ n = Num n
pattern `_ x = Var x
pattern _+_ x y = Add x y
pattern _·_ x y = Mul x y
pattern Let_≔_In_ x e f = Let x e f

infix 50 $_ `_
infixr 30 _·_
infixl 25 _+_
infixr 20 Let_≔_In_
infixl 20 _ResultIs_

private
  variable
    e e₀ e₁ f : AExp
    c c₀ c₁ d : Cmd
```

We have a new construct `c ResultIs e` which evaluates the program `c` and then evaluates to expression `e`.
In order to keep track of the new state caused by evaluating `c`, we will need to propagate the state around.
Since the evaluation of programs is not a total function,
we will develop a big-steps operational semantics.

```
infix 4 _,_⇒A_,_ _,_⇒B_,_  _,_⇒_

data _,_⇒A_,_ : AExp → State → ℕ → State → Set
data _,_⇒_ : Cmd → State → State → Set 

data _,_⇒A_,_ where

  ⇒-Num :
    -----------------
    Num n , s ⇒A n , s

  ⇒-Var :
    --------------------
    Var x , s ⇒A s x , s

  ⇒-Add :
    e , s ⇒A m , s′ →
    f , s′ ⇒A n , s″ →
    -----------------------
    e + f , s ⇒A m +ℕ n , s″

  ⇒-Mul :
    e , s ⇒A m , s′ →
    f , s′ ⇒A n , s″ →
    -----------------------
    e · f , s ⇒A m ·ℕ n , s″ 

  ⇒-Let :
    e , s ⇒A m , s′ →
    f , s′ [ x ↦ m ] ⇒A n , s″ →
    ---------------------
    Let x e f , s ⇒A n , s″

  →-ResultIs :
    c , s ⇒ s′ →
    e , s′ ⇒A n , s″ →
    -------------------------
    c ResultIs e , s ⇒A n , s″

```

## Boolean expressions

```
data BExp : Set where
  tt : BExp
  ff : BExp
  Not : BExp → BExp
  Or : BExp → BExp → BExp
  And : BExp → BExp → BExp
  Leq : AExp → AExp → BExp

private
  variable
    b b₀ b₁ : BExp
    v v₀ v₁  : 𝔹
```

```
data _,_⇒B_,_ : BExp → State → 𝔹 → State → Set where

  ⇒-tt :
    ---------------
    tt , s ⇒B tt , s

  ⇒-ff :
    ---------------
    ff , s ⇒B ff , s

  ⇒-Not :
    b , s ⇒B v , s′ →
    ----------------------
    Not b , s ⇒B ¬𝔹 v , s′

  ⇒-Or :
    b₀ , s ⇒B v₀ , s′ →
    b₁ , s′ ⇒B v₁ , s″ →
    -----------------------------
    Or b₀ b₁ , s ⇒B v₀ ∨𝔹 v₁ , s″

  ⇒-And :
    b₀ , s ⇒B v₀ , s′ →
    b₁ , s′ ⇒B v₁ , s″ →
    -----------------------------
    And b₀ b₁ , s ⇒B v₀ ∧𝔹 v₁ , s″

  ⇒-Leq :
    e₀ , s ⇒A n₀ , s′ →
    e₁ , s′ ⇒A n₁ , s″ →
    ----------------------------------
    Leq e₀ e₁ , s ⇒B ⌞ n₀ ≤? n₁ ⌟ , s″
```

## Programs

```
infixr 20 _⨟_
infix 25 _≔_

data Cmd where
  skip : Cmd
  _≔_ : VarName → AExp → Cmd
  _⨟_ : Cmd → Cmd → Cmd
  if_then_else_ : BExp → Cmd → Cmd → Cmd
  while_do:_ : BExp → Cmd → Cmd
```

```
data _,_⇒_  where

  ⇒-skip :
    ------------
    skip , s ⇒ s

  ⇒-assign :
    e , s ⇒A n , s′ →
    -------------------------
    x ≔ e , s ⇒ s′ [ x ↦ n ]

  ⇒-seq :
    c , s ⇒ s′ →
    d , s′ ⇒ s″ →
    ---------------
    c ⨟ d , s ⇒ s″

  ⇒-if-tt :
    b , s ⇒B tt , s′ →
    c , s′ ⇒ s″ →
    ---------------------------
    if b then c else d , s ⇒ s″
    
  ⇒-if-ff :
    b , s ⇒B ff , s′ →
    d , s′ ⇒ s″ →
    ---------------------------
    if b then c else d , s ⇒ s″

  ⇒-while-tt :
    b , s ⇒B tt , s′ →
    c , s′ ⇒ s″ →
    while b do: c , s″ ⇒ s‴ →
    --------------------------
    while b do: c , s ⇒ s‴
  
  ⇒-while-ff :
    b , s ⇒B ff , s′ →
    ---------------------
    while b do: c , s ⇒ s′
```
