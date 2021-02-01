---
title: "Arithmetic and Boolean expressions 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Exp where
open import part0.index hiding (AExp; A⟦_⟧; _≈_) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _≤_ to _≤ℕ_) public
```

# Arithmetic expressions

We develop an eager denotational and operational semantics
for a simple language of arithmetic expressions,
and we prove that they agree.

## Variables

We represent *variable names* as natural Number.
Any countable domain with decidable equality (such as strings) would work here

```
VarName = ℕ

x₀ x₁ : VarName
x₀ = 0
x₁ = 1

private variable x y z : VarName
```

## Syntax of expressions

We define a minimalistic language of arithmetic expressions
comprising variables and a let assignment construct.

```
data AExp : Set where
  Num : (n : ℕ) → AExp
  Var : (x : VarName) → AExp
  Add : (e f : AExp) → AExp
  Mul : (e f : AExp) → AExp
  Let : (x : VarName) (e f : AExp) → AExp

private
  variable
    e e′ f f′ g : AExp
    m n : ℕ
```

For example,
the following expression adds one to a variable (called 10).
This is pure syntax so far, no calculation is being performed.

```
add-one : AExp
add-one = Add (Var 10) (Num 1)
```

```
pattern $_ n = Num n
pattern `_ x = Var x
pattern _+_ x y = Add x y
pattern _·_ x y = Mul x y
pattern Let_≔_In_ x e f = Let x e f

infix 50 $_ `_
infixr 30 _·_
infixl 25 _+_
infixr 20 Let_≔_In_
```

```
add-one′ : AExp
add-one′ = ` 10 + $ 1
```

## Environments

In order to represent the value of free variables,
we use environments.

```
Env = VarName → ℕ

private variable ϱ ϱ′ : Env
```

The following environment assigns value `200` to the variable named `10`,
and value `40` to every other variable.

```
ϱ₀ : Env
ϱ₀ 10 = 200
ϱ₀ _ = 40
```

# Boolean expressions

On top of arithmetic expressions we can build a simple language of Boolean expressions.
An element in `BExp` is a boolean combination
of atomic expressions of the form `Leq e f`,
where `e` and `f` are arithmetic expressions.

```
data BExp : Set where
  tt : BExp
  ff : BExp
  Not : BExp → BExp
  Or : BExp → BExp → BExp
  And : BExp → BExp → BExp
  Leq : AExp → AExp → BExp

pattern _∨_ b₀ b₁ = Or b₀ b₁
pattern _∧_ b₀ b₁ = And b₀ b₁
pattern ¬_ b = Not b
pattern _≤_ e f = Leq e f
```

# Denotational semantics

```
infix 15 ⟦_⟧_ A⟦_⟧_
private ⟦_⟧_ : AExp → Env → ℕ
⟦ $ n ⟧ ϱ = n
⟦ ` x ⟧ ϱ = ϱ x
⟦ e + f ⟧ ϱ = ⟦ e ⟧ ϱ +ℕ ⟦ f ⟧ ϱ
⟦ e · f ⟧ ϱ = ⟦ e ⟧ ϱ ·ℕ ⟦ f ⟧ ϱ
⟦ Let x e f ⟧ ϱ = ⟦ f ⟧ ϱ [ x ↦ ⟦ e ⟧ ϱ ]

A⟦_⟧_ = ⟦_⟧_
```

With our denotational semantics for expressions we can check (by computation) the value of concrete expressions.

```
_ : ⟦ add-one ⟧ ϱ₀ ≡ 201
_ = refl
```

!exercise(#exercise:BExp-semantics)
~~~~~~~~~~~~~~~~

Write the denotational semantics of Boolean expressions.

```
infix 101 B⟦_⟧_
B⟦_⟧_ : BExp → Env → 𝔹
```

!codemirror(BExp-semantics)(B⟦_⟧_)

*Hint:* In the `Leq` case you will need `_≤?_`.

~~~~~~~~~~~~~~~~
~~~~~~~~~~~~~~~~

We proceed by structural induction on Boolan expressions.

```
B⟦ tt ⟧ ρ = tt
B⟦ ff ⟧ ρ = ff
B⟦ ¬ b ⟧ ρ = ¬𝔹 B⟦ b ⟧ ρ
B⟦ b ∨ c ⟧ ρ = B⟦ b ⟧ ρ ∨𝔹 B⟦ c ⟧ ρ
B⟦ b ∧ c ⟧ ρ = B⟦ b ⟧ ρ ∧𝔹 B⟦ c ⟧ ρ
B⟦ e ≤ f ⟧ ρ
  with A⟦ e ⟧ ρ ≤? A⟦ f ⟧ ρ
... | yes _ = tt
... | no _ = ff
```

~~~~~~~~~~~~~~~~

# Lazy semantics

## Dynamic binding

```
Envˡ = VarName → AExp

ϱ₁ : Envˡ
ϱ₁ _ = $ 0

infix 15 ⟦_⟧ˡ_

{-# TERMINATING #-}
⟦_⟧ˡ_ : AExp → Envˡ → ℕ
⟦ $ n ⟧ˡ ϱ = n
⟦ ` x ⟧ˡ ϱ = ⟦ ϱ x ⟧ˡ ϱ -- termination issue here
⟦ e + f ⟧ˡ ϱ = ⟦ e ⟧ˡ ϱ +ℕ ⟦ f ⟧ˡ ϱ
⟦ e · f ⟧ˡ ϱ = ⟦ e ⟧ˡ ϱ ·ℕ ⟦ f ⟧ˡ ϱ
⟦ Let x e f ⟧ˡ ϱ = ⟦ f ⟧ˡ ϱ [ x ↦ e ]
```

Example:

```
_ : ⟦ Let x₀ ($ 2 + $ 3) ($ 3 · ` x₀) ⟧ˡ ϱ₁ ≡ 15
_  = refl
```

Notice how the meaning of free variables dynamically depends on the environment active when they are *used*:

```
_ : ⟦ Let x₁ ≔ $ 1 In Let x₀ ≔ ` x₁ In Let x₁ ≔ $ 2 In ` x₀ ⟧ˡ ϱ₁ ≡ 2
_  = refl
```

## Static binding

We need coinductively-defined environments.

```
-- Envˡˢ = VarName → AExp × Envˡˢ
```

```
record Envˡˢ : Set where
  coinductive
  field
    env : VarName → AExp × Envˡˢ

open Envˡˢ

_[[_↦_,_]] : Envˡˢ → VarName → AExp → Envˡˢ → Envˡˢ
env (ϱ [[ x ↦ e , ϱ′ ]]) = env ϱ [ x ↦ e , ϱ′ ]
```

```
ϱ₂ : Envˡˢ
env ϱ₂ _ = $ 0 , ϱ₂

infix 15 ⟦_⟧ˡˢ_

{-# TERMINATING #-}
⟦_⟧ˡˢ_ : AExp → Envˡˢ → ℕ
⟦ $ n ⟧ˡˢ ϱ = n
⟦ ` x ⟧ˡˢ ϱ = let e , ϱ′ = env ϱ x in ⟦ e ⟧ˡˢ ϱ′ -- termination issue
⟦ e + f ⟧ˡˢ ϱ = ⟦ e ⟧ˡˢ ϱ +ℕ ⟦ f ⟧ˡˢ ϱ
⟦ e · f ⟧ˡˢ ϱ = ⟦ e ⟧ˡˢ ϱ ·ℕ ⟦ f ⟧ˡˢ ϱ
⟦ Let x e f ⟧ˡˢ ϱ = ⟦ f ⟧ˡˢ ϱ [[ x ↦ e , ϱ ]]
```

Notice how the meaning of free variables statically depends on the environment active when they are *defined*:

```
_ : ⟦ Let x₁ ≔ $ 1 In Let x₀ ≔ ` x₁ In Let x₁ ≔ $ 2 In ` x₀ ⟧ˡˢ ϱ₂ ≡ 1
_  = refl
```

We show that the lazy semantics with static binding agrees with the eager semantics.
Note that in general the lazy semantics may be "more defined" than the eager one, i.e., in the presence of errors or exceptions.

```
env-agree : Envˡˢ → Env → Set
env-agree ϱ τ = ∀[ x ] ⟦ ` x ⟧ˡˢ ϱ ≡ τ x

env-agree-update : ∀ ϱ τ x e → env-agree ϱ τ → env-agree (ϱ [[ x ↦ e , ϱ ]]) (τ [ x ↦ ⟦ e ⟧ˡˢ ϱ ])
env-agree-update ϱ τ x e ag y
  with x ≡? y
... | yes refl = refl
... | no _ = ag y

eager-lazy-agree : ∀ ϱ τ → env-agree ϱ τ → ∀[ e ] ⟦ e ⟧ˡˢ ϱ ≡ ⟦ e ⟧ τ
eager-lazy-agree _ _ ag ($ n) = refl
eager-lazy-agree _ _ ag (` x) = ag x
eager-lazy-agree ϱ τ ag (e + f)
  rewrite eager-lazy-agree ϱ τ ag e |
          eager-lazy-agree ϱ τ ag f = refl
eager-lazy-agree ϱ τ ag (e · f)
  rewrite eager-lazy-agree ϱ τ ag e |
          eager-lazy-agree ϱ τ ag f = refl
eager-lazy-agree ϱ τ ag (Let x ≔ e In f)
  with env-agree-update ϱ τ x e ag
... | ag′
  rewrite sym (eager-lazy-agree ϱ τ ag e) |
          eager-lazy-agree (ϱ [[ x ↦ e , ϱ ]]) (τ [ x ↦ ⟦ e ⟧ˡˢ ϱ ]) ag′ f = refl
```

# Free variables

```
fv : AExp → VarName *
fv ($ n) = ε
fv (` x) = [ x ]
fv (e + f) = fv e ++ fv f
fv (e · f) = fv e ++ fv f
fv (Let x e f) = fv e ++ remove x (fv f)

closed : AExp → Set
closed e = fv e ≡ ε

fv-lemma : ∀ ϱ₀ ϱ₁ e → Agree ϱ₀ ϱ₁ (fv e) → ⟦ e ⟧ ϱ₀ ≡ ⟦ e ⟧ ϱ₁
fv-lemma = {!   !}

-- all named variables occurring in the expression
vars : AExp → VarName *
vars ($ n) = ε
vars (` x) = [ x ]
vars (e + f) = fv e ++ fv f
vars (e · f) = fv e ++ fv f
vars (Let x e f) = [ x ] ++ fv e ++ fv f
```

# Substitution

We say that two arithmetic expression are *contextually equivalent* if they provide the same result whenever they are plugged in the same context.

```
infix 101 _A[_↦_]
_A[_↦_] : AExp → VarName → AExp → AExp

($ n) A[ x ↦ g ] = $ n

(` y) A[ x ↦ g ]
  with x ≡? y
... | yes _ = g
... | no _ = ` y

(e + f) A[ x ↦ g ] = e A[ x ↦ g ] + f A[ x ↦ g ]
(e · f) A[ x ↦ g ] = e A[ x ↦ g ] · f A[ x ↦ g ]

Let y e f A[ x ↦ g ]
  with e A[ x ↦ g ]
... | e′
  with x ≡? y
... | yes _ = Let y e′ f
... | no _ = Let y e′ (f A[ x ↦ g ]) -- in general this is incorrect since free variables in g may get captured
```

Substitution facts:

```
subs-Let-1 : ∀ x e → Let x e f A[ x ↦ g ] ≡ Let x (e A[ x ↦ g ]) f
subs-Let-1 x e = {!   !}
```

This is correct only if no free occurrence of `x` in `e` falls under a let binding a variable `y` which is free in `g`.
This is captured by `g AdmissibleFor x In e`.

```
_NotFreeIn_ : VarName → AExp → Set
x NotFreeIn e = x ~∈ fv e

infix 20 _AdmissibleFor_In_
data _AdmissibleFor_In_ (g : AExp) (x : VarName) : AExp → Set where

  Num : (n : ℕ) → g AdmissibleFor x In $ n

  Var : (y : VarName) → g AdmissibleFor x In ` y

  Add : ∀ e f →
        g AdmissibleFor x In e → 
        g AdmissibleFor x In f → 
        ----------------------------
        g AdmissibleFor x In (e + f)

  Mul : ∀ e f →
        g AdmissibleFor x In e → 
        g AdmissibleFor x In f → 
        ----------------------------
        g AdmissibleFor x In (e · f)

  Let-1 : ∀ e f →
          g AdmissibleFor x In e → 
          --------------------------------
          g AdmissibleFor x In (Let x e f)

  Let-2 : ∀ e f →
          x ≢ y →
          x NotFreeIn f →
          g AdmissibleFor x In e →
          --------------------------------
          g AdmissibleFor x In (Let y e f)

  Let-3 : ∀ e f →
          x ≢ y →
          y NotFreeIn g →
          g AdmissibleFor x In e →
          g AdmissibleFor x In f →
          --------------------------------
          g AdmissibleFor x In (Let y e f)

subst-lemma : ∀ g x ϱ →
  g AdmissibleFor x In e →
  --------------------------------------------
  ⟦ e A[ x ↦ g ] ⟧ ϱ ≡ ⟦ e ⟧ ϱ [ x ↦ ⟦ g ⟧ ϱ ]

subst-lemma _ _ _ (Num n) = refl

subst-lemma _ x _ (Var y)
  with x ≡? y
... | yes refl = refl
... | no _ = refl

subst-lemma g x ϱ (Add e f adm-e adm-f)
  rewrite subst-lemma g x ϱ adm-e |
          subst-lemma g x ϱ adm-f
  = refl

subst-lemma g x ϱ (Mul e f adm-e adm-f)
  rewrite subst-lemma g x ϱ adm-e |
          subst-lemma g x ϱ adm-f
  = refl

subst-lemma g x ϱ (Let-1 e f adm-e)
  with subst-lemma g x ϱ adm-e
... | ind =
  begin
    ⟦ Let x e f A[ x ↦ g ] ⟧ ϱ
      ≡⟨ cong (λ C → ⟦ C ⟧ ϱ) (subs-Let-1 x e) ⟩
    ⟦ Let x (e A[ x ↦ g ]) f ⟧ ϱ
      ≡⟨⟩
    ⟦ f ⟧ ϱ [ x ↦ ⟦ e A[ x ↦ g ] ⟧ ϱ ]
      ≡⟨ cong (λ C → ⟦ f ⟧ ϱ [ x ↦ C ]) ind ⟩
    ⟦ f ⟧ ϱ [ x ↦ ⟦ e ⟧ ϱ [ x ↦ ⟦ g ⟧ ϱ ] ]
      ≡⟨ cong (λ C → ⟦ f ⟧ C) (sym (doubleupdate x)) ⟩
    ⟦ f ⟧ ϱ [ x ↦ ⟦ g ⟧ ϱ ] [ x ↦ ⟦ e ⟧ ϱ [ x ↦ ⟦ g ⟧ ϱ ] ]
      ≡⟨⟩
    ⟦ Let x e f ⟧ ϱ [ x ↦ ⟦ g ⟧ ϱ ]
  ∎

subst-lemma g x ϱ (Let-2 e f x≢y xNFf adm-e) = {!   !}

subst-lemma g x ϱ (Let-3 e f x≢y yNFg adm-e adm-f) = {!   !}

-- subst-lemma ($ n) = refl

-- subst-lemma {x} (` y)
--   with x ≡? y
-- ... | yes refl = refl
-- ... | no _ = refl

-- subst-lemma {x} {g} {ϱ} (e + f)
--   rewrite subst-lemma {x} {g} {ϱ} e |
--           subst-lemma {x} {g} {ϱ} f = refl

-- subst-lemma {x} {g} {ϱ} (e · f)
--   rewrite subst-lemma {x} {g} {ϱ} e |
--           subst-lemma {x} {g} {ϱ} f = refl

-- subst-lemma {x} {g} {ϱ} (Let y e f)
--   with x ≡? y
-- ... | yes refl = 
--   begin
--   ⟦ Let x (e A[ x ↦ g ]) f ⟧ ϱ
--     ≡⟨⟩
--   ⟦ f ⟧ ϱ [ x ↦ ⟦ e A[ x ↦ g ] ⟧ ϱ ]
--     ≡⟨ cong (λ C → ⟦ f ⟧ ϱ [ x ↦ C ]) (subst-lemma {x} {g} {ϱ} e) ⟩
--   ⟦ f ⟧ ϱ [ x ↦ ⟦ e ⟧ ϱ′ ]
--     ≡⟨ cong (λ C → ⟦ f ⟧ C) (sym (doubleupdate x)) ⟩
--   ⟦ f ⟧ ϱ′ [ x ↦ ⟦ e ⟧ ϱ′ ]
--     ≡⟨⟩
--   ⟦ Let x e f ⟧ ϱ′
--   ∎ where ϱ′ = ϱ [ x ↦ ⟦ g ⟧ ϱ ]

-- ... | no x≢y
--   with y ∈? fv g
-- ... | no ¬y∈g =
--   begin
--   ⟦ Let y (e A[ x ↦ g ]) (f A[ x ↦ g ]) ⟧ ϱ
--     ≡⟨⟩
--   ⟦ f A[ x ↦ g ] ⟧ ϱ [ y ↦ ⟦ e A[ x ↦ g ] ⟧ ϱ ]
--     ≡⟨ cong (λ C → ⟦ f A[ x ↦ g ] ⟧ ϱ [ y ↦ C ]) (subst-lemma e) ⟩
--   ⟦ f A[ x ↦ g ] ⟧ ϱ′′
--     ≡⟨ subst-lemma f ⟩
--   ⟦ f ⟧ ϱ′′ [ x ↦ ⟦ g ⟧ ϱ′′ ]
--     ≡⟨⟩
--   ⟦ f ⟧ ϱ [ y ↦ ⟦ e ⟧ ϱ′ ] [ x ↦ ⟦ g ⟧ ϱ′′ ]
--     ≡⟨ sym (cong (λ C → ⟦ f ⟧ C) (update-comm _ _ _ _ _  x≢y))⟩
--   ⟦ f ⟧ ϱ [ x ↦ ⟦ g ⟧ ϱ′′ ] [ y ↦ ⟦ e ⟧ ϱ′ ] 
--     ≡⟨ cong (λ C → ⟦ f ⟧ ϱ [ x ↦ C ] [ y ↦ ⟦ e ⟧ ϱ′ ]) eq ⟩
--   ⟦ f ⟧ ϱ [ x ↦ ⟦ g ⟧ ϱ ] [ y ↦ ⟦ e ⟧ ϱ′ ]
--     ≡⟨⟩
--   ⟦ f ⟧ ϱ′ [ y ↦ ⟦ e ⟧ ϱ′ ]
--     ≡⟨⟩
--   ⟦ Let y e f ⟧ ϱ′
--   ∎ where ϱ′ = ϱ [ x ↦ ⟦ g ⟧ ϱ ]
--           ϱ′′ = ϱ [ y ↦ ⟦ e ⟧ ϱ′ ]

--           ag : Agree ϱ ϱ′′ (fv g)
--           ag = Agree-update-~∈ ¬y∈g

--           eq : ⟦ g ⟧ ϱ′′ ≡ ⟦ g ⟧ ϱ
--           eq = fv-lemma ϱ′′ ϱ g (sym-Agree ag)

-- ... | yes y∈g = {!   !}
```

# Contextual equivalence and full abstraction

```
private _≈_ : ∀ e f → Set
e ≈ f = ∀ c x ϱ → ⟦ c A[ x ↦ e ] ⟧ ϱ ≡ ⟦ c A[ x ↦ f ] ⟧ ϱ
```

There is nothing else beside the numerical value an expression has.

```
full-abstraction-1 : e ≈ f → ∀[ ϱ ] ⟦ e ⟧ ϱ ≡ ⟦ f ⟧ ϱ
full-abstraction-1 e≈f ϱ = e≈f (` x₀) x₀ ϱ

full-abstraction-2 : ∀[ ϱ ] ⟦ e ⟧ ϱ ≡ ⟦ f ⟧ ϱ → e ≈ f

full-abstraction-2 ⟦e⟧≡⟦f⟧ ($ n) x ϱ = refl

full-abstraction-2 ⟦e⟧≡⟦f⟧ (` y) x ϱ
  with x ≡? y
... | yes refl = ⟦e⟧≡⟦f⟧ ϱ
... | no _ = refl

full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ (c + d) x ϱ
  rewrite full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ c x ϱ |
          full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ d x ϱ = refl

full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ (c · d) x ϱ
  rewrite full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ c x ϱ |
          full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ d x ϱ = refl

full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ (Let y c d) x ϱ
  with x ≡? y
... | yes refl
  rewrite full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ c y ϱ = refl
... | no _
  rewrite full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ c x ϱ |
          full-abstraction-2 {e} {f} ⟦e⟧≡⟦f⟧ d x (ϱ [ y ↦ ⟦ c A[ x ↦ f ] ⟧ ϱ ]) = refl

full-abstraction : e ≈ f ↔ ∀[ ϱ ] ⟦ e ⟧ ϱ ≡ A⟦ f ⟧ ϱ
full-abstraction = full-abstraction-1 , full-abstraction-2
```

# Small-steps operational semantics

## Global environment

We use global environments and eager semantics.

```
infix 4 _⊢_↝_
data _⊢_↝_ : Env → AExp → AExp → Set where

  ↝-Var : ϱ ⊢ ` x ↝ $ ϱ x

  ↝-Add-stop :
    ϱ ⊢ $ m + $ n ↝ $ (m +ℕ n)

  ↝-Add-left :
    ϱ ⊢ e ↝ e′ →
    ------------------
    ϱ ⊢ e + f ↝ e′ + f

  ↝-Add-right :
    ϱ ⊢ f ↝ f′ →
    ------------------
    ϱ ⊢ e + f ↝ e + f′

  ↝-Mul-stop :
    ϱ ⊢ $ m · $ n ↝ $ (m ·ℕ n)

  ↝-Mul-left :
    ϱ ⊢ e ↝ e′ →
    ------------------
    ϱ ⊢ e · f ↝ e′ · f

  ↝-Mul-right :
    ϱ ⊢ f ↝ f′ →
    ------------------
    ϱ ⊢ e · f ↝ e · f′

  ↝-Let-stop :
    ϱ ⊢ Let x ($ m) ($ n) ↝ $ n

  ↝-Let-1 :
    ϱ [ x ↦ m ] ⊢ f ↝ f′ →
    ----------------------------------
    ϱ ⊢ Let x ($ m) f ↝ Let x ($ m) f′

  ↝-Let-2 :
    ϱ ⊢ e ↝ e′ →
    --------------------------
    ϱ ⊢ Let x e f ↝ Let x e′ f
```

### Preservation

```
preservation :
  ϱ ⊢ e ↝ f →
  -----------------
  ⟦ e ⟧ ϱ ≡ ⟦ f ⟧ ϱ

preservation ↝-Var = refl

preservation ↝-Add-stop = refl
preservation (↝-Add-left step) rewrite preservation step = refl
preservation (↝-Add-right step) rewrite preservation step = refl

preservation ↝-Mul-stop = refl
preservation (↝-Mul-left step) rewrite preservation step = refl
preservation (↝-Mul-right step) rewrite preservation step = refl

preservation ↝-Let-stop = refl
preservation (↝-Let-1 step) rewrite preservation step = refl
preservation (↝-Let-2 step) rewrite preservation step = refl
```

### Transitive closure

We define the transitive closure of the small-step operational semantics.

```
data _⊢_↝*_ : Env → AExp → AExp → Set where

    stop : ϱ ⊢ e ↝* e

    one : ϱ ⊢ e ↝ f →
          ϱ ⊢ f ↝* g →
          ----------
          ϱ ⊢ e ↝* g
```

We can indeed show that `_⊢_↝*_` is transitive with a standard induction.

```
↝*-trans :
  ϱ ⊢ e ↝* f →
  ϱ ⊢ f ↝* g →
  ----------
  ϱ ⊢ e ↝* g

↝*-trans stop δ = δ
↝*-trans (one step δ₁) δ₂ = one step (↝*-trans δ₁ δ₂)
```

An easy induction based on !ref(preservation) shows that the denotational semantics is preserved by the transitive closure of the small-step operational semantics.

```
preservation* :
  ϱ ⊢ e ↝* f →
  -----------------
  ⟦ e ⟧ ϱ ≡ ⟦ f ⟧ ϱ

preservation* {ϱ} {e} {.e} stop = refl
preservation* {ϱ} {e} {g} (one {f = f} step der) =
    begin
        ⟦ e ⟧ ϱ ≡⟨ preservation {ϱ} {e} {f} step ⟩
        ⟦ f ⟧ ϱ ≡⟨ preservation* {ϱ} {f} {g} der ⟩
        ⟦ g ⟧ ϱ
    ∎
```

This immediately implies that whenever the small-step semantics terminates producing a number `m`,
then this is the right result.

```
↝*-agree-⟦⟧ :
  ϱ ⊢ e ↝* $ m →
  --------------
  m ≡ ⟦ e ⟧ ϱ

↝*-agree-⟦⟧ der = sym (preservation* der)
```

### Deterministic values

Notice that small-step semantics is a non-deterministic relation:
In general there may be several ways to reduce an expression
(as witnessed by the rules `↝-Add-left` and `↝-Add-right` for instance).

However, as an immediate consequence of preservation
we have that if two numerical values are eventually produced,
then they necessarily are the same number.

```
↝*-det :
  ϱ ⊢ e ↝* Num m →
  ϱ ⊢ e ↝* Num n →
  -----------------
  m ≡ n

↝*-det der1 der2 rewrite sym (preservation* der1) | preservation* der2 = refl
```

### Congruence

We show that the transitive closure `_⊢_↝*_` respects subexpressions.

```
add-cong-1 :
  ϱ ⊢ e ↝* e′ →
  -------------------
  ϱ ⊢ e + f ↝* e′ + f

add-cong-1 stop = stop
add-cong-1 (one x d) = one (↝-Add-left x) (add-cong-1 d)

add-cong-2 :
  ϱ ⊢ f ↝* f′ →
  -------------------
  ϱ ⊢ e + f ↝* e + f′

add-cong-2 stop = stop
add-cong-2 (one x d) = one (↝-Add-right x) (add-cong-2 d)

mul-cong-1 :
  ϱ ⊢ e ↝* e′ →
  -------------------
  ϱ ⊢ e · f ↝* e′ · f

mul-cong-1 stop = stop
mul-cong-1 (one x d) = one (↝-Mul-left x) (mul-cong-1 d)

mul-cong-2 :
  ϱ ⊢ f ↝* f′ →
  -------------------
  ϱ ⊢ e · f ↝* e · f′

mul-cong-2 stop = stop
mul-cong-2 (one x d) = one (↝-Mul-right x) (mul-cong-2 d)

let-cong-1 :
  ϱ ⊢ e ↝* e′ →
  ----------------------------
  ϱ ⊢ Let x e f ↝* Let x e′ f

let-cong-1 stop = stop
let-cong-1 (one x d) = one (↝-Let-2 x) (let-cong-1 d)

let-cong-2 :
  ϱ [ x ↦ m ] ⊢ f ↝* f′ →
  -----------------------------------
  ϱ ⊢ Let x ($ m) f ↝* Let x ($ m) f′

let-cong-2 stop = stop
let-cong-2 (one x d) = one (↝-Let-1 x) (let-cong-2 d)
```

### Relational reasoning

We introduce some syntactic sugaring to conveniently write chains of small steps.

```
infixr 2 _↝*⟨⟩_ _↝*⟨_⟩_ _↝⟨_⟩_ 
infix  3 _↝*∎

_↝*⟨⟩_ : ∀ {ϱ} e {f} → ϱ ⊢ e ↝* f → ϱ ⊢ e ↝* f
e ↝*⟨⟩ e↝*f = e↝*f

_↝*⟨_⟩_ : ∀ {ϱ} e {f g} → ϱ ⊢ e ↝* f → ϱ ⊢ f ↝* g → ϱ ⊢ e ↝* g
e ↝*⟨ e↝*f ⟩ f↝*g = ↝*-trans e↝*f f↝*g

_↝⟨_⟩_ : ∀ {ϱ} e {f g} → ϱ ⊢ e ↝ f → ϱ ⊢ f ↝* g → ϱ ⊢ e ↝* g
e ↝⟨ e↝f ⟩ f↝*g = e ↝*⟨ one e↝f stop ⟩ f↝*g 

_↝*∎ : ∀ e → ϱ ⊢ e ↝* e
e ↝*∎ = stop
```

### **Exercise**: Termination (Weak normalisation)

So far we have shown that the small-step semantics produces the right result,
*if it produces any result at all*.
In fact, an operational semantics that never reaches a Numerical value
trivially satisfies this condition.

We prove that the small step operational semantics can always reache some numerical value after a finite number of steps.
In other word, we prove below that the rewrite is *weakly normalising*.

```
weak-normalisation : ∀ e → ϱ ⊢ e ↝* $ (⟦ e ⟧ ϱ)

weak-normalisation ($ n) = stop

weak-normalisation (` x) = one ↝-Var stop

weak-normalisation {ϱ} (e + f)
  with weak-normalisation e | weak-normalisation f
... | de | df = 
  e + f ↝*⟨ add-cong-1 de ⟩
  ($ (⟦ e ⟧ ϱ)) + f ↝*⟨ add-cong-2 df ⟩
  ($ (⟦ e ⟧ ϱ)) + ($ (⟦ f ⟧ ϱ)) ↝⟨ ↝-Add-stop ⟩
  $ (⟦ e ⟧ ϱ +ℕ ⟦ f ⟧ ϱ)
  ↝*∎

weak-normalisation {ϱ} (e · f)
  with weak-normalisation e | weak-normalisation f
... | de | df = 
  e · f ↝*⟨ mul-cong-1 de ⟩
  ($ (⟦ e ⟧ ϱ)) · f ↝*⟨ mul-cong-2 df ⟩
  ($ (⟦ e ⟧ ϱ)) · ($ (⟦ f ⟧ ϱ)) ↝⟨ ↝-Mul-stop ⟩
  $ (⟦ e ⟧ ϱ ·ℕ ⟦ f ⟧ ϱ)
  ↝*∎

weak-normalisation {ϱ} (Let x e f)
  with weak-normalisation e | weak-normalisation f
... | de | df =
    Let x e f ↝*⟨ let-cong-1 de ⟩
    Let x ($ (⟦ e ⟧ ϱ)) f ↝*⟨ let-cong-2 df ⟩
    Let x ($ (⟦ e ⟧ ϱ)) ($ (⟦ f ⟧ (ϱ [ x ↦ ⟦ e ⟧ ϱ ])))
        ↝⟨ ↝-Let-stop ⟩
    $ (⟦ f ⟧ (ϱ [ x ↦ ⟦ e ⟧ ϱ ]))
    ↝*∎
```

### **Exercise**: Strong normalisation

The termination property above is also called *weak normalisation*,
which means that there exists a finite reduction sequence `e ↝* f`
reaching a normal form (i.e. a value) `f ≡ Num m`.
We show below even *strong normalisation*, namely,
*every* reduction sequence starting from `e` is finite.

To this end, we introduce a notion of *size* of arithmetic expressions.

```
size : AExp → ℕ
size (Num x) = 0
size (Var x) = 1
size (Add e f) = 1 +ℕ size e +ℕ size f
size (Mul e f) = 1 +ℕ size e +ℕ size f
size (Let x e f) = 1 +ℕ size e +ℕ size f
```

In the lemma below we show that the size of an expression strictly decreases at each step, which implies strong normalisation.

```
size-down :
  ϱ ⊢ e ↝ f →
  ---------------
  size e > size f
  
size-down ↝-Var = s≤s 0≤n

size-down ↝-Add-stop = s≤s 0≤n
size-down (↝-Add-left δ) = s≤s (<-+-left (size-down δ))
size-down {e = e + _} (↝-Add-right δ) = s≤s (<-+-right {n = size e} (size-down δ))

size-down ↝-Mul-stop = s≤s 0≤n
size-down (↝-Mul-left δ) = s≤s (<-+-left (size-down δ))
size-down {e = e · _} (↝-Mul-right δ) = s≤s (<-+-right {n = size e} (size-down δ))

size-down ↝-Let-stop = s≤s 0≤n
size-down (↝-Let-1 δ) = s≤s (size-down δ)
size-down (↝-Let-2 δ) = s≤s (<-+-left (size-down δ))
```

In the two "right" cases we need to give some extra hint for one implicit parameter.

## Local environments

An alternative way to deal with the environment is to use it in a local way.
However this causes troubles.
The naive way to write the derivation rules is incorrect:

```
infix 4 _,_↝_,_
data _,_↝_,_ : AExp → Env → AExp → Env → Set where

  ↝-Var : ` x , ϱ ↝ $ ϱ x , ϱ

  ↝-Add-stop :
    $ m + $ n , ϱ ↝ $ (m +ℕ n) , ϱ

  ↝-Add-left :
    e , ϱ ↝ e′ , ϱ′ →
    -----------------------
    e + f , ϱ ↝ e′ + f , ϱ′

  ↝-Add-right :
    f , ϱ ↝ f′ , ϱ′ →
    ------------------
    e + f , ϱ ↝ e + f′ , ϱ′

  ↝-Let-stop :
    Let x ($ m) ($ n) , ϱ ↝ $ n , ϱ

  ↝-Let-1 :
    f , ϱ [ x ↦ m ] ↝ f′ , ϱ′ →
    ---------------------------------------
    Let x ($ m) f , ϱ ↝ Let x ($ m) f′ , ϱ′

  ↝-Let-2 :
    e , ϱ ↝ e′ , ϱ′ →
    ------------------------------
    Let x e f , ϱ ↝ Let x e′ f , ϱ′
```

One option would be to add a new construct in the language `e then x is n` to save and restore the previous value of `x`.

# Big-steps operational semantics

```
infix 4 _,_⇒_
data _,_⇒_ : AExp → Env → ℕ → Set where

  ⇒-Num :
    -------------
    Num n , ϱ ⇒ n

  ⇒-Var :
    ---------------
    Var x , ϱ ⇒ ϱ x

  ⇒-Add :
    e , ϱ ⇒ m →
    f , ϱ ⇒ n →
    ------------------
    e + f , ϱ ⇒ m +ℕ n

  ⇒-Mul :
    e , ϱ ⇒ m →
    f , ϱ ⇒ n →
    ------------------
    e · f , ϱ ⇒ m ·ℕ n

  ⇒-Let :
    e , ϱ ⇒ m →
    f , ϱ [ x ↦ m ] ⇒ n →
    ---------------------
    Let x e f , ϱ ⇒ n
```

Example derivation:

```
x0 = 0
e0 = Let x0 ($ 2 + $ 3) (` x0 · $ 2) 

_ : e0 , ϱ₀ ⇒ 10
_ = BEGIN
    have $ 2 , ϱ₀ ⇒ 2                               by ⇒-Num
    have $ 3 , ϱ₀ ⇒ 3                               by ⇒-Num
    have $ 2 + $ 3 , ϱ₀ ⇒ 5                         apply ⇒-Add at back 1 , here

    have ` x0 , ϱ₀ [ x0 ↦ 5 ] ⇒ 5                   by ⇒-Var
    have $ 2 , ϱ₀ [ x0 ↦ 5 ] ⇒ 2                    by ⇒-Num
    have (` x0 · $ 2) , ϱ₀ [ x0 ↦ 5 ] ⇒ 10          apply ⇒-Mul at back 1 , here

    have Let x0 ($ 2 + $ 3) (` x0 · $ 2) , ϱ₀ ⇒ 10  apply ⇒-Let at back 3 , here
    END
```

## Evaluator (interpreter)

Luckily we can automatically produce the derivations as in the previous example.

```
eval : ∀ e ϱ → ∃[ n ] e , ϱ ⇒ n

eval ($ n) ϱ = n , ⇒-Num

eval (` x) ϱ = ϱ x , ⇒-Var

eval (e + f) ϱ
  with eval e ϱ | eval f ϱ
... | m , δ | n , σ = m +ℕ n , ⇒-Add δ σ

eval (e · f) ϱ
  with eval e ϱ | eval f ϱ
... | m , δ | n , σ = m ·ℕ n , ⇒-Mul δ σ

eval (Let x e f) ϱ
  with eval e ϱ
... | m , δ 
  with eval f (ϱ [ x ↦ m ])
... | n , σ = n , ⇒-Let δ σ
```

```
_ : e0 , ϱ₀ ⇒ 10
_ = dsnd (eval e0 ϱ₀)
```

## Evaluation is deterministic

```
⇒-det :
  e , ϱ ⇒ m →
  e , ϱ ⇒ n →
  -----------
  m ≡ n

⇒-det ⇒-Num ⇒-Num = refl
⇒-det ⇒-Var ⇒-Var = refl
⇒-det (⇒-Add x x₁) (⇒-Add y y₁)
    with ⇒-det x y | ⇒-det x₁ y₁
... | refl | refl = refl
⇒-det (⇒-Mul x x₁) (⇒-Mul y y₁)
    with ⇒-det x y | ⇒-det x₁ y₁
... | refl | refl = refl
⇒-det (⇒-Let ⇒₁-e ⇒₁-f) (⇒-Let ⇒₂-e ⇒₂-f)
    with ⇒-det ⇒₁-e ⇒₂-e
... | refl
    with ⇒-det ⇒₁-f ⇒₂-f
... | refl = refl
```

Note that in the `⇒-Let` case we cannot perform the two with-abstractions in parallel because in order to apply the second one `⇒-det ⇒₁-f ⇒₂-f`
we need the result of the first one.

## Agreement of the semantics

The following lemma shows that the big-steps operational semantics agrees with the denotational semantics.

```
⇒-agree-⟦⟧ : e , ϱ ⇒ ⟦ e ⟧ ϱ
⇒-agree-⟦⟧ {Num x} = ⇒-Num
⇒-agree-⟦⟧ {Var x} = ⇒-Var
⇒-agree-⟦⟧ {Add e e₁} = ⇒-Add ⇒-agree-⟦⟧ ⇒-agree-⟦⟧ 
⇒-agree-⟦⟧ {Mul e e₁} = ⇒-Mul ⇒-agree-⟦⟧ ⇒-agree-⟦⟧ 
⇒-agree-⟦⟧ {Let x e f} = ⇒-Let ⇒-agree-⟦⟧ ⇒-agree-⟦⟧
```

# Binary numbers

## LSD

```
data LSD : Set where
  $ : LSD
  _𝟬 : LSD → LSD
  _𝟭 : LSD → LSD
```

Semantics according to least significant digit (LSD)

```
LSD⟦_⟧ : LSD → ℕ
LSD⟦ $ ⟧ = 0
LSD⟦ x 𝟬 ⟧ = 2 ·ℕ LSD⟦ x ⟧
LSD⟦ x 𝟭 ⟧ = suc (2 ·ℕ LSD⟦ x ⟧)
```

Example:

```
_ : LSD⟦ $ 𝟬 𝟭 𝟭 𝟬 ⟧ ≡ 6
_ = refl
```

## MSD

```
data MSD : Set where
  $ : MSD
  𝟬_ : MSD → MSD
  𝟭_ : MSD → MSD
```

Semantics according to most significant digit (MSD).
This won't work:

```
-- MSD⟦_⟧ : MSD → ℕ
-- MSD⟦ x ⟧ = {!   !}
```

A possible solution: Additionally remember the number of digits (second component).

```
MSD⟦_⟧ : MSD → ℕ × ℕ
MSD⟦ $ ⟧ = 0 , 0
MSD⟦ 𝟬 x ⟧
  with MSD⟦ x ⟧
... | n , k = n , suc k

MSD⟦ 𝟭 x ⟧
  with MSD⟦ x ⟧
... | n , k = n +ℕ 2 ^ k , suc k
```

Example:

```
_ : MSD⟦ 𝟬 𝟭 𝟭 𝟬 $ ⟧ ≡ 6 , 4 
_ = refl
```

## Agreement of LSD and MSD

```
push-𝟬 push-𝟭 : MSD → MSD
push-𝟬 $ = 𝟬 $
push-𝟬 (𝟬 x) = 𝟬 (push-𝟬 x)
push-𝟬 (𝟭 x) = 𝟭 (push-𝟬 x)

push-𝟭 $ = 𝟭 $
push-𝟭 (𝟬 x) = 𝟬 (push-𝟭 x)
push-𝟭 (𝟭 x) = 𝟭 (push-𝟭 x)

-- this type was copied-pasted and abstracted from the goal in push-𝟬-lemma  before the last rewrite
aux-𝟬 : ∀ m n → m +ℕ (m +ℕ 0) +ℕ (n +ℕ (n +ℕ zero)) ≡ m +ℕ n +ℕ (m +ℕ n +ℕ 0)
aux-𝟬 = solve-∀

push-𝟬-lemma : ∀ x → let n , k = MSD⟦ x ⟧ in MSD⟦ push-𝟬 x ⟧ ≡ 2 ·ℕ n , suc k
push-𝟬-lemma $ = refl
push-𝟬-lemma (𝟬 x) rewrite push-𝟬-lemma x = refl
push-𝟬-lemma (𝟭 x)
  rewrite push-𝟬-lemma x |
          aux-𝟬 (fst MSD⟦ x ⟧) (2 ^ snd MSD⟦ x ⟧) = refl

aux-𝟭 : ∀ m n → suc (m +ℕ (m +ℕ 0) +ℕ (n +ℕ (n +ℕ zero))) ≡ suc (m +ℕ n +ℕ (m +ℕ n +ℕ 0))
aux-𝟭 = solve-∀

push-𝟭-lemma : ∀ x → let n , k = MSD⟦ x ⟧ in MSD⟦ push-𝟭 x ⟧ ≡ suc (2 ·ℕ n) , suc k
push-𝟭-lemma $ = refl
push-𝟭-lemma (𝟬 x) rewrite push-𝟭-lemma x = refl
push-𝟭-lemma (𝟭 x)
  rewrite push-𝟭-lemma x |
          aux-𝟭 (fst MSD⟦ x ⟧) (2 ^ snd MSD⟦ x ⟧) = refl

LSD2MSD : LSD → MSD
LSD2MSD $ = $
LSD2MSD (x 𝟬) = push-𝟬 (LSD2MSD x)
LSD2MSD (x 𝟭) = push-𝟭 (LSD2MSD x) 

LSD-MSD-agree : ∀ x → LSD⟦ x ⟧ ≡ fst MSD⟦ LSD2MSD x ⟧

LSD-MSD-agree $ = refl

LSD-MSD-agree (x 𝟬)
  with LSD-MSD-agree x
... | ind
  rewrite push-𝟬-lemma (LSD2MSD x) |
          sym ind = refl

LSD-MSD-agree (x 𝟭)
  with LSD-MSD-agree x
... | ind
  rewrite push-𝟭-lemma (LSD2MSD x) |
          sym ind = refl
```

# Binary expressions

## Syntax

```
infix 30 _𝟬 _𝟭

data Bin : Set where
  $ : Bin
  _𝟬 : Bin → Bin
  _𝟭 : Bin → Bin
  Add : Bin → Bin → Bin

pattern _+_ x y = Add x y

private
  variable
    a a′ b b′ : Bin
```

## Denotational semantics

```
private ⟦_⟧ : Bin → ℕ
⟦ $ ⟧ = 0
⟦ a 𝟬 ⟧ = 2 ·ℕ ⟦ a ⟧
⟦ a 𝟭 ⟧ = 1 +ℕ 2 ·ℕ ⟦ a ⟧
⟦ a + b ⟧ = ⟦ a ⟧ +ℕ ⟦ b ⟧
```

## Small-steps operational semantics

```
infix 4 _↝_
data _↝_ : Bin → Bin → Set where

  ↝𝟬 : a ↝ a′ →
       ----------
       a 𝟬 ↝ a′ 𝟬

  ↝𝟭 : a ↝ a′ →
       ----------
       a 𝟭 ↝ a′ 𝟭

  ↝$L : ---------
        $ + a ↝ a

  ↝$R : ---------
        a + $ ↝ a

  ↝+L : a ↝ a′ →
        --------------
        a + b ↝ a′ + b

  ↝+R : b ↝ b′ →
        --------------
        a + b ↝ a + b′
        
  ↝+𝟬𝟬 : ---------------------
         a 𝟬 + b 𝟬 ↝ (a + b) 𝟬

  ↝+𝟬𝟭 : ---------------------
         a 𝟬 + b 𝟭 ↝ (a + b) 𝟭

  ↝+𝟭𝟬 : ---------------------
         a 𝟭 + b 𝟬 ↝ (a + b) 𝟭

  ↝+𝟭𝟭 : ----------------------------
         a 𝟭 + b 𝟭 ↝ (a + b + $ 𝟭) 𝟬
```

## Agreement 

```
agree : a ↝ a′ →
        --------------
        ⟦ a ⟧ ≡ ⟦ a′ ⟧

agree (↝𝟬 e↝e') rewrite agree e↝e' = refl
agree (↝𝟭 e↝e') rewrite agree e↝e' = refl
agree ↝$L = refl
agree ↝$R = n+0≡n _
agree (↝+L e↝e') rewrite agree e↝e' = refl
agree (↝+R e↝e') rewrite agree e↝e' = refl
agree (↝+𝟬𝟬 {a} {b}) = magic ⟦ a ⟧ ⟦ b ⟧ where

  magic : ∀ a b → a +ℕ (a +ℕ zero) +ℕ (b +ℕ (b +ℕ 0)) ≡ a +ℕ b +ℕ (a +ℕ b +ℕ 0)
  magic = solve-∀

agree (↝+𝟬𝟭 {a} {b}) = magic ⟦ a ⟧ ⟦ b ⟧ where
    
    magic : ∀ a b → a +ℕ (a +ℕ 0) +ℕ suc (b +ℕ (b +ℕ 0)) ≡ suc (a +ℕ b +ℕ (a +ℕ b +ℕ 0))
    magic = solve-∀

agree (↝+𝟭𝟬 {a} {b}) = magic ⟦ a ⟧ ⟦ b ⟧ where
    
    magic : ∀ a b → suc (a +ℕ (a +ℕ 0) +ℕ (b +ℕ (b +ℕ 0))) ≡ suc (a +ℕ b +ℕ (a +ℕ b +ℕ 0))
    magic = solve-∀
    
agree (↝+𝟭𝟭 {a} {b}) = magic ⟦ a ⟧ ⟦ b ⟧ where

  magic : ∀ a b → suc (a +ℕ (a +ℕ 0) +ℕ suc (b +ℕ (b +ℕ 0))) ≡ a +ℕ b +ℕ 1 +ℕ (a +ℕ b +ℕ 1 +ℕ 0)
  magic = solve-∀
```

## Strong normalisation (first proof)

```
binSize : Bin → ℕ
binSize $ = 0
binSize (a 𝟬) = 1 +ℕ binSize a
binSize (a 𝟭) = 1 +ℕ binSize a
binSize (a + b) = 1 +ℕ binSize a +ℕ binSize b

-- transitive closure
-- infix 4 _↝*_
-- data _↝*_ : Bin → Bin → Set where
--     stop : ∀ {a} → a ↝* a
--     one : ∀ {a b g} → a ↝ b → b ↝* g → a ↝* g

-- strong normalisation
-- we define a measure that is strictly decreasing on each computation step

μ : Bin → ℕ
μ $ = 0
μ (a 𝟬) = 2 +ℕ μ a
μ (a 𝟭) = 4 +ℕ μ a
μ (a + b) = 1 +ℕ μ a +ℕ μ b

μ-wf : a ↝ b →
       ---------
       μ b < μ a

μ-wf (↝𝟬 e↝f) with μ-wf e↝f
... | μf<μe = s≤s (s≤s μf<μe)

μ-wf (↝𝟭 e↝f) with μ-wf e↝f
... | μf<μe = s≤s (s≤s (s≤s (s≤s μf<μe)))

μ-wf ↝$L = refl-≤

μ-wf .{a + $} {a} ↝$R rewrite n+0≡n (μ a) = refl-≤

μ-wf (↝+L e↝e') with μ-wf e↝e'
... | μe'<μe = s≤s (<-+-left μe'<μe)

μ-wf (↝+R f↝f') with μ-wf f↝f'
... | μf'<μf = s≤s (<-+-right μf'<μf)

μ-wf {a} {b} ↝+𝟬𝟬 = s≤s (s≤s (s≤s (<-+-right n<suc2n)))

μ-wf a@{Add (a₁ 𝟬) (b₁ 𝟭)} {b} ↝+𝟬𝟭
  rewrite
    n+0≡n (μ a) |
    n+0≡n (μ b) |
    suc-lemma {μ a₁} {suc (suc (suc (μ b₁)))} |
    suc-lemma {μ a₁} {suc (suc (μ b₁))} |
    suc-lemma {μ a₁} {suc (μ b₁)} |
    suc-lemma {μ a₁} {μ b₁}
  = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s n≤sucn)))))

μ-wf a@{Add (a₁ 𝟭) (b₁ 𝟬)} {b} ↝+𝟭𝟬
  rewrite
    n+0≡n (μ a) |
    n+0≡n (μ b) |
    suc-lemma {μ a₁} {suc (μ b₁)} |
    suc-lemma {μ a₁} {μ b₁}
  = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s n≤sucn)))))

μ-wf a@{Add (a₁ 𝟭) (b₁ 𝟭)} {b} ↝+𝟭𝟭 = goal where

  magic : ∀ a b →
      suc (suc (suc (suc (suc (a +ℕ b +ℕ 4))))) ≡
      suc (suc (suc (suc (suc (a +ℕ suc (suc (suc (suc b))))))))
  magic = {! solve-∀ !}

  goal : suc (suc (suc (suc (suc (μ a₁ +ℕ μ b₁ +ℕ 4))))) ≤ℕ
         suc (suc (suc (suc (suc (μ a₁ +ℕ suc (suc (suc (suc (μ b₁)))))))))
  goal rewrite magic (μ a₁) (μ b₁) = refl-≤
```

## Strong normalisation (second proof)

We prove strong normalisation by well-founded induction on a lexicograpic order.

```
zeroes ones dollars : Bin → ℕ

zeroes $ = 0
zeroes (a 𝟬) = 1 +ℕ zeroes a
zeroes (a 𝟭) = zeroes a
zeroes (a + b) = zeroes a +ℕ zeroes b

ones $ = 0
ones (a 𝟬) = ones a
ones (a 𝟭) = 1 +ℕ ones a
ones (a + b) = ones a +ℕ ones b

dollars $ = 1
dollars (a 𝟬) = dollars a
dollars (a 𝟭) = dollars a
dollars (a + b) = dollars a +ℕ dollars b

Triple = ℕ × ℕ × ℕ

triple : Bin → Triple
triple a = (ones a , zeroes a , dollars a)

_≺_ : Triple → Triple → Set
_≺_ = _<_ ×ₗₑₓ _<_ ×ₗₑₓ _<_

wf-≺ : WellFounded _≺_
wf-≺ = lex-wf <-wf (lex-wf <-wf <-wf)

triple-mon : a ↝ b →
             -------------------
             triple b ≺ triple a
             
triple-mon (↝𝟬 δ) with triple-mon δ
... | left 1s = left 1s
... | right (1s , left 0s) = right (1s , left (s≤s 0s))
... | right (1s , right (0s , $s)) = right (1s , right (cong suc 0s , $s))

triple-mon (↝𝟭 δ) with triple-mon δ
... | left 1s = left (s≤s 1s)
... | right (1s , left 0s) = right (cong suc 1s , left 0s)
... | right (1s , right (0s , $s)) = right (cong suc 1s , right (0s , $s))

triple-mon {$ + b} ↝$L = right (refl , right (refl , n<sucn))

triple-mon {b + $} ↝$R
  rewrite
    n+0≡n (ones b) |
    n+0≡n (zeroes b) |
    suc-lemma {dollars b} {0} |
    n+0≡n (dollars b) = right (refl , right (refl , refl-≤))

triple-mon (↝+L δ) with triple-mon δ
... | left 1s = left (<-+-left 1s)
... | right (1s , left 0s) rewrite 1s = right (refl , left (<-+-left 0s))
... | right (1s , right (0s , $s)) rewrite 1s | 0s = right (refl , right (refl , <-+-left $s))

triple-mon (↝+R δ) with triple-mon δ
... | left 1s = left (<-+-right 1s)
... | right (1s , left 0s) rewrite 1s | 1s = right (refl , left (<-+-right 0s))
... | right (1s , right (0s , $s)) rewrite 1s | 1s | 0s = right (refl , right (refl , <-+-right $s))

-- number of zeroes goes down
triple-mon {a 𝟬 + b 𝟬} ↝+𝟬𝟬 rewrite suc-lemma {zeroes a} {zeroes b} = right ( refl , left refl-≤)

-- number of zeroes goes down
triple-mon {a 𝟬 + b 𝟭} ↝+𝟬𝟭 rewrite suc-lemma {ones a} {ones b} = right ( refl , left refl-≤)

-- number of zeroes goes down
triple-mon {a 𝟭 + b 𝟬} ↝+𝟭𝟬 rewrite suc-lemma {zeroes a} {zeroes b} = right ( refl , left refl-≤)

-- number of ones goes down
triple-mon {a 𝟭 + b 𝟭} ↝+𝟭𝟭 = left goal where

  have : ∀ a b → suc (a +ℕ b +ℕ 1) ≡ suc (a +ℕ suc b)
  have = {! solve-∀ !}

  goal : suc (ones a +ℕ ones b +ℕ 1) ≤ℕ suc (ones a +ℕ suc (ones b))
  goal rewrite have (ones a) (ones b) = refl-≤
```