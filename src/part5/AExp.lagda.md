---
title: "Arithmetic expressions 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.AExp where
open import part0.index hiding (AExp) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_) public
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

infix 50 $_ `_
infixr 30 _·_
infixl 25 _+_
```

## Environments

In order to represent the value of free variables,
we use environments.

```
Env = VarName → ℕ

private variable ρ : Env
```

The following environment assigns value `200` to the variable named `10`,
and value `40` to every other variable.

```
ρ0 : Env
ρ0 10 = 200
ρ0 _ = 40
```

# Denotational semantics

```
infix 15 ⟦_⟧_
⟦_⟧_ : AExp → Env → ℕ
⟦ $ n ⟧ ρ = n
⟦ ` x ⟧ ρ = ρ x
⟦ e + f ⟧ ρ = ⟦ e ⟧ ρ +ℕ ⟦ f ⟧ ρ
⟦ e · f ⟧ ρ = ⟦ e ⟧ ρ ·ℕ ⟦ f ⟧ ρ
⟦ Let x e f ⟧ ρ = ⟦ f ⟧ ρ [ x ↦ ⟦ e ⟧ ρ ]
```

With our denotational semantics for expressions we can check (by computation) the value of concrete expressions.

```
_ : ⟦ add-one ⟧ ρ0 ≡ 201
_ = refl
```

# Small-steps operational semantics

We use global environments and eager semantics.

```
infix 4 _⊢_↝_
data _⊢_↝_ : Env → AExp → AExp → Set where

  ↝-Var : ρ ⊢ ` x ↝ $ ρ x

  ↝-Add-stop :
    ρ ⊢ $ m + $ n ↝ $ (m +ℕ n)

  ↝-Add-left :
    ρ ⊢ e ↝ e′ →
    ------------------
    ρ ⊢ e + f ↝ e′ + f

  ↝-Add-right :
    ρ ⊢ f ↝ f′ →
    ------------------
    ρ ⊢ e + f ↝ e + f′

  ↝-Mul-stop :
    ρ ⊢ $ m · $ n ↝ $ (m ·ℕ n)

  ↝-Mul-left :
    ρ ⊢ e ↝ e′ →
    ------------------
    ρ ⊢ e · f ↝ e′ · f

  ↝-Mul-right :
    ρ ⊢ f ↝ f′ →
    ------------------
    ρ ⊢ e · f ↝ e · f′

  ↝-Let-stop :
    ρ ⊢ Let x ($ m) ($ n) ↝ $ n

  ↝-Let-1 :
    ρ [ x ↦ m ] ⊢ f ↝ f′ →
    ----------------------------------
    ρ ⊢ Let x ($ m) f ↝ Let x ($ m) f′

  ↝-Let-2 :
    ρ ⊢ e ↝ e′ →
    --------------------------
    ρ ⊢ Let x e f ↝ Let x e′ f
```

## Preservation

```
preservation :
  ρ ⊢ e ↝ f →
  -----------------
  ⟦ e ⟧ ρ ≡ ⟦ f ⟧ ρ

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

## Transitive closure

We define the transitive closure of the small-step operational semantics.

```
data _⊢_↝*_ : Env → AExp → AExp → Set where

    stop : ρ ⊢ e ↝* e

    one : ρ ⊢ e ↝ f →
          ρ ⊢ f ↝* g →
          ----------
          ρ ⊢ e ↝* g
```

We can indeed show that `_⊢_↝*_` is transitive with a standard induction.

```
↝*-trans :
  ρ ⊢ e ↝* f →
  ρ ⊢ f ↝* g →
  ----------
  ρ ⊢ e ↝* g

↝*-trans stop δ = δ
↝*-trans (one step δ₁) δ₂ = one step (↝*-trans δ₁ δ₂)
```

An easy induction based on !ref(preservation) shows that the denotational semantics is preserved by the transitive closure of the small-step operational semantics.

```
preservation* :
  ρ ⊢ e ↝* f →
  -----------------
  ⟦ e ⟧ ρ ≡ ⟦ f ⟧ ρ

preservation* {ρ} {e} {.e} stop = refl
preservation* {ρ} {e} {g} (one {f = f} step der) =
    begin
        ⟦ e ⟧ ρ ≡⟨ preservation {ρ} {e} {f} step ⟩
        ⟦ f ⟧ ρ ≡⟨ preservation* {ρ} {f} {g} der ⟩
        ⟦ g ⟧ ρ
    ∎
```

This immediately implies that whenever the small-step semantics terminates producing a number `m`,
then this is the right result.

```
↝*-agree-⟦⟧ :
  ρ ⊢ e ↝* $ m →
  --------------
  m ≡ ⟦ e ⟧ ρ

↝*-agree-⟦⟧ der = sym (preservation* der)
```

## Deterministic values

Notice that small-step semantics is a non-deterministic relation:
In general there may be several ways to reduce an expression
(as witnessed by the rules `↝-Add-left` and `↝-Add-right` for instance).

However, as an immediate consequence of preservation
we have that if two numerical values are eventually produced,
then they necessarily are the same number.

```
↝*-det :
  ρ ⊢ e ↝* Num m →
  ρ ⊢ e ↝* Num n →
  -----------------
  m ≡ n

↝*-det der1 der2 rewrite sym (preservation* der1) | preservation* der2 = refl
```

## Congruence

We show that the transitive closure `_⊢_↝*_` respects subexpressions.

```
add-cong-1 :
  ρ ⊢ e ↝* e′ →
  -------------------
  ρ ⊢ e + f ↝* e′ + f

add-cong-1 stop = stop
add-cong-1 (one x d) = one (↝-Add-left x) (add-cong-1 d)

add-cong-2 :
  ρ ⊢ f ↝* f′ →
  -------------------
  ρ ⊢ e + f ↝* e + f′

add-cong-2 stop = stop
add-cong-2 (one x d) = one (↝-Add-right x) (add-cong-2 d)

mul-cong-1 :
  ρ ⊢ e ↝* e′ →
  -------------------
  ρ ⊢ e · f ↝* e′ · f

mul-cong-1 stop = stop
mul-cong-1 (one x d) = one (↝-Mul-left x) (mul-cong-1 d)

mul-cong-2 :
  ρ ⊢ f ↝* f′ →
  -------------------
  ρ ⊢ e · f ↝* e · f′

mul-cong-2 stop = stop
mul-cong-2 (one x d) = one (↝-Mul-right x) (mul-cong-2 d)

let-cong-1 :
  ρ ⊢ e ↝* e′ →
  ----------------------------
  ρ ⊢ Let x e f ↝* Let x e′ f

let-cong-1 stop = stop
let-cong-1 (one x d) = one (↝-Let-2 x) (let-cong-1 d)

let-cong-2 :
  ρ [ x ↦ m ] ⊢ f ↝* f′ →
  -----------------------------------
  ρ ⊢ Let x ($ m) f ↝* Let x ($ m) f′

let-cong-2 stop = stop
let-cong-2 (one x d) = one (↝-Let-1 x) (let-cong-2 d)
```

## Relational reasoning

We introduce some syntactic sugaring to conveniently write chains of small steps.

```
infixr 2 _↝*⟨⟩_ _↝*⟨_⟩_ _↝⟨_⟩_ 
infix  3 _↝*∎

_↝*⟨⟩_ : ∀ {ρ} e {f} → ρ ⊢ e ↝* f → ρ ⊢ e ↝* f
e ↝*⟨⟩ e↝*f = e↝*f

_↝*⟨_⟩_ : ∀ {ρ} e {f g} → ρ ⊢ e ↝* f → ρ ⊢ f ↝* g → ρ ⊢ e ↝* g
e ↝*⟨ e↝*f ⟩ f↝*g = ↝*-trans e↝*f f↝*g

_↝⟨_⟩_ : ∀ {ρ} e {f g} → ρ ⊢ e ↝ f → ρ ⊢ f ↝* g → ρ ⊢ e ↝* g
e ↝⟨ e↝f ⟩ f↝*g = e ↝*⟨ one e↝f stop ⟩ f↝*g 

_↝*∎ : ∀ e → ρ ⊢ e ↝* e
e ↝*∎ = stop
```

## **Exercise**: Termination (Weak normalisation)

So far we have shown that the small-step semantics produces the right result,
*if it produces any result at all*.
In fact, an operational semantics that never reaches a Numerical value
trivially satisfies this condition.

We prove that the small step operational semantics can always reache some numerical value after a finite number of steps.
In other word, we prove below that the rewrite is *weakly normalising*.

```
weak-normalisation : ∀ e → ρ ⊢ e ↝* $ (⟦ e ⟧ ρ)

weak-normalisation ($ n) = stop

weak-normalisation (` x) = one ↝-Var stop

weak-normalisation {ρ} (e + f)
  with weak-normalisation e | weak-normalisation f
... | de | df = 
  e + f ↝*⟨ add-cong-1 de ⟩
  ($ (⟦ e ⟧ ρ)) + f ↝*⟨ add-cong-2 df ⟩
  ($ (⟦ e ⟧ ρ)) + ($ (⟦ f ⟧ ρ)) ↝⟨ ↝-Add-stop ⟩
  $ (⟦ e ⟧ ρ +ℕ ⟦ f ⟧ ρ)
  ↝*∎

weak-normalisation {ρ} (e · f)
  with weak-normalisation e | weak-normalisation f
... | de | df = 
  e · f ↝*⟨ mul-cong-1 de ⟩
  ($ (⟦ e ⟧ ρ)) · f ↝*⟨ mul-cong-2 df ⟩
  ($ (⟦ e ⟧ ρ)) · ($ (⟦ f ⟧ ρ)) ↝⟨ ↝-Mul-stop ⟩
  $ (⟦ e ⟧ ρ ·ℕ ⟦ f ⟧ ρ)
  ↝*∎

weak-normalisation {ρ} (Let x e f)
  with weak-normalisation e | weak-normalisation f
... | de | df =
    Let x e f ↝*⟨ let-cong-1 de ⟩
    Let x ($ (⟦ e ⟧ ρ)) f ↝*⟨ let-cong-2 df ⟩
    Let x ($ (⟦ e ⟧ ρ)) ($ (⟦ f ⟧ (ρ [ x ↦ ⟦ e ⟧ ρ ])))
        ↝⟨ ↝-Let-stop ⟩
    $ (⟦ f ⟧ (ρ [ x ↦ ⟦ e ⟧ ρ ]))
    ↝*∎
```

## **Exercise**: Strong normalisation

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
  ρ ⊢ e ↝ f →
  ---------------
  size e > size f
  
size-down ↝-Var = s≤s 0≤n

size-down ↝-Add-stop = s≤s 0≤n
size-down (↝-Add-left de) = {!   !} -- s≤s (≤-+-cong-1 (size-down de))
size-down {ρ} {e + f} {e + f′} (↝-Add-right de)
  with size-down de -- | suc-lemma (size e) (size f′)
... | e>f = {!   !} -- s≤s (subst (_≤ size e + size f) (sym p) {! ≤-+-cong-2 e>f !})

size-down ↝-Mul-stop = s≤s 0≤n
size-down (↝-Mul-left δ) = {!   !} -- s≤s (≤-+-cong-1 (size-down de))
size-down {ρ} {e · f} {e · f′} (↝-Mul-right δ)
  with size-down δ 
... | e>f = {!   !}

size-down ↝-Let-stop = s≤s 0≤n
size-down (↝-Let-1 de) = s≤s (size-down de)
size-down (↝-Let-2 de) = s≤s {!   !} -- (≤-+-cong-1 (size-down de))
```

# Big-steps operational semantics

```
infix 4 _,_⇒_
data _,_⇒_ : AExp → Env → ℕ → Set where
  ⇒-Num : ∀ {n ρ} → Num n , ρ ⇒ n
  ⇒-Var : ∀ {x ρ} → Var x , ρ ⇒ ρ x
  ⇒-Add : ∀ {e f m n ρ} → e , ρ ⇒ m → f , ρ ⇒ n → Add e f , ρ ⇒ m +ℕ n
  ⇒-let : ∀ {x e f m n ρ} → e , ρ ⇒ m → f , ρ [ x ↦ m ] ⇒ n
         → Let x e f , ρ ⇒ n
```

## Evaluation is deterministic

```
⇒-det : ∀ {e ρ m n} → e , ρ ⇒ m → e , ρ ⇒ n → m ≡ n
⇒-det ⇒-Num ⇒-Num = refl
⇒-det ⇒-Var ⇒-Var = refl
⇒-det (⇒-Add x x₁) (⇒-Add y y₁)
    with ⇒-det x y | ⇒-det x₁ y₁
... | refl | refl = refl
⇒-det (⇒-let ⇒₁-e ⇒₁-f) (⇒-let ⇒₂-e ⇒₂-f)
    with ⇒-det ⇒₁-e ⇒₂-e
... | refl
    with ⇒-det ⇒₁-f ⇒₂-f
... | refl = refl
```

Note that in the `⇒-let` case we cannot perform the two with-abstractions in parallel because in order to apply the second one `⇒-det ⇒₁-f ⇒₂-f`
we need the result of the first one.

## Agreement of the semantics

The following lemma shows that the big-steps operational semantics agrees with the denotational semantics.

```
⇒-agree-⟦⟧ : ∀ {e ρ} → e , ρ ⇒ ⟦ e ⟧ ρ
⇒-agree-⟦⟧ {Num x} = ⇒-Num
⇒-agree-⟦⟧ {Var x} = ⇒-Var
⇒-agree-⟦⟧ {Add e e₁} = ⇒-Add ⇒-agree-⟦⟧ ⇒-agree-⟦⟧ 
⇒-agree-⟦⟧ {Mul e e₁} = {!   !} -- ⇒-Add ⇒-agree-⟦⟧ ⇒-agree-⟦⟧ 
⇒-agree-⟦⟧ {Let x e f} = ⇒-let ⇒-agree-⟦⟧ ⇒-agree-⟦⟧
```