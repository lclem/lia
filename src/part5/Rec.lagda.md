---
title: "Recursion expressions 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Rec where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _≤_ to _≤ℕ_) public
```

```
VarName = ℕ
FunName = ℕ

x₀ x₁ : VarName
x₀ = 0
x₁ = 1

data Exp : Set where
  Num : (n : ℕ) → Exp
  Var : (x : VarName) → Exp
  Add : (e f : Exp) → Exp
  Let : (x : VarName) (e f : Exp) → Exp
  Rec : (f : FunName) (e f : Exp) → Exp

private
  variable
    e e′ f f′ g : Exp
    m n : ℕ
```

```
pattern $_ n = Num n
pattern `_ x = Var x
pattern _+_ x y = Add x y
pattern Let_≔_In_ x e f = Let x e f
pattern Rec_≔_In_ f e g = Rec f e g

infix 50 $_ `_
infixl 25 _+_
infixr 20 Let_≔_In_ Rec_≔_In_
```

# Eager semantics