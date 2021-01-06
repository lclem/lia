---
title: "Arithmetic expressions 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.AExp where
open import part0.index hiding (AExp; A⟦_⟧; _≈_) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_) public
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

```
add-one′ : AExp
add-one′ = ` 10 + $ 1
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
infix 15 ⟦_⟧_ A⟦_⟧_
private ⟦_⟧_ sem : AExp → Env → ℕ
⟦ $ n ⟧ ρ = n
⟦ ` x ⟧ ρ = ρ x
⟦ e + f ⟧ ρ = ⟦ e ⟧ ρ +ℕ ⟦ f ⟧ ρ
⟦ e · f ⟧ ρ = ⟦ e ⟧ ρ ·ℕ ⟦ f ⟧ ρ
⟦ Let x e f ⟧ ρ = ⟦ f ⟧ ρ [ x ↦ ⟦ e ⟧ ρ ]

A⟦_⟧_ = ⟦_⟧_
sem = ⟦_⟧_
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

# Big-steps operational semantics

```
infix 4 _,_⇒_
data _,_⇒_ : AExp → Env → ℕ → Set where

  ⇒-Num :
    -------------
    Num n , ρ ⇒ n

  ⇒-Var :
    ---------------
    Var x , ρ ⇒ ρ x

  ⇒-Add :
    e , ρ ⇒ m →
    f , ρ ⇒ n →
    ------------------
    e + f , ρ ⇒ m +ℕ n

  ⇒-Mul :
    e , ρ ⇒ m →
    f , ρ ⇒ n →
    ------------------
    e · f , ρ ⇒ m ·ℕ n

  ⇒-Let :
    e , ρ ⇒ m →
    f , ρ [ x ↦ m ] ⇒ n →
    ---------------------
    Let x e f , ρ ⇒ n
```

Example derivation:

```
x0 = 0
e0 = Let x0 ($ 2 + $ 3) (` x0 · $ 2) 

_ : e0 , ρ0 ⇒ 10
_ = BEGIN
    have $ 2 , ρ0 ⇒ 2                               by ⇒-Num
    have $ 3 , ρ0 ⇒ 3                               by ⇒-Num
    have $ 2 + $ 3 , ρ0 ⇒ 5                         apply ⇒-Add at back 1 , here

    have ` x0 , ρ0 [ x0 ↦ 5 ] ⇒ 5                   by ⇒-Var
    have $ 2 , ρ0 [ x0 ↦ 5 ] ⇒ 2                    by ⇒-Num
    have (` x0 · $ 2) , ρ0 [ x0 ↦ 5 ] ⇒ 10          apply ⇒-Mul at back 1 , here

    have Let x0 ($ 2 + $ 3) (` x0 · $ 2) , ρ0 ⇒ 10  apply ⇒-Let at back 3 , here
    END
```

## Evaluator (interpreter)

Luckily we can automatically produce the derivations as in the previous example.

```
eval : ∀ e ρ → ∃[ n ] e , ρ ⇒ n

eval ($ n) ρ = n , ⇒-Num

eval (` x) ρ = ρ x , ⇒-Var

eval (e + f) ρ
  with eval e ρ | eval f ρ
... | m , δ | n , σ = m +ℕ n , ⇒-Add δ σ

eval (e · f) ρ
  with eval e ρ | eval f ρ
... | m , δ | n , σ = m ·ℕ n , ⇒-Mul δ σ

eval (Let x e f) ρ
  with eval e ρ
... | m , δ 
  with eval f (ρ [ x ↦ m ])
... | n , σ = n , ⇒-Let δ σ
```

```
_ : e0 , ρ0 ⇒ 10
_ = dsnd (eval e0 ρ0)
```

## Evaluation is deterministic

```
⇒-det :
  e , ρ ⇒ m →
  e , ρ ⇒ n →
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
⇒-agree-⟦⟧ : e , ρ ⇒ ⟦ e ⟧ ρ
⇒-agree-⟦⟧ {Num x} = ⇒-Num
⇒-agree-⟦⟧ {Var x} = ⇒-Var
⇒-agree-⟦⟧ {Add e e₁} = ⇒-Add ⇒-agree-⟦⟧ ⇒-agree-⟦⟧ 
⇒-agree-⟦⟧ {Mul e e₁} = ⇒-Mul ⇒-agree-⟦⟧ ⇒-agree-⟦⟧ 
⇒-agree-⟦⟧ {Let x e f} = ⇒-Let ⇒-agree-⟦⟧ ⇒-agree-⟦⟧
```

## Contextual equivalence

We say that two arithmetic expression are *contextually equivalent* if they provide the same result whenever they are plugged in the same context.

```
fv : AExp → VarName *
fv ($ n) = ε
fv (` x) = [ x ]
fv (e + f) = fv e ++ fv f
fv (e · f) = fv e ++ fv f
fv (Let x e f) = fv e ++ remove x (fv f)

closed : AExp → Set
closed e = fv e ≡ ε

fv-lemma : ∀ ρ₀ ρ₁ e → Agree ρ₀ ρ₁ (fv e) → ⟦ e ⟧ ρ₀ ≡ ⟦ e ⟧ ρ₁
fv-lemma = {!   !}

-- all named variables occurring in the expression
vars : AExp → VarName *
vars ($ n) = ε
vars (` x) = [ x ]
vars (e + f) = fv e ++ fv f
vars (e · f) = fv e ++ fv f
vars (Let x e f) = [ x ] ++ fv e ++ fv f

-- fresh : AExp → VarName
-- fresh = {!   !}

-- fresh2 : AExp → AExp → VarName
-- fresh2 = {!   !}

-- fresh-lemma : ∀ e → fresh e ~∈ vars e
-- fresh-lemma = {!   !}

-- fresh2-lemma : ∀ e f → fresh2 e f ~∈ vars e × fresh2 e f ~∈ vars f
-- fresh2-lemma = {!   !}

-- rename : AExp → VarName → VarName → AExp
-- rename e x y = {!   !}

-- refresh : AExp → AExp → AExp
-- refresh e g = {!   !}

-- refresh-lemma : let e′ = refresh e g in sem e ≡ sem e′ × vars e′ ∩ vars g ≡ ε
-- refresh-lemma = {!   !}

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

## Substitution facts

```
subs-Let-1 : ∀ x e → Let x e f A[ x ↦ g ] ≡ Let x (e A[ x ↦ g ]) f
subs-Let-1 x e = {!   !}
```

## Substitution lemma

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

subst-lemma : ∀ g x ρ →
  g AdmissibleFor x In e →
  --------------------------------------------
  ⟦ e A[ x ↦ g ] ⟧ ρ ≡ ⟦ e ⟧ ρ [ x ↦ ⟦ g ⟧ ρ ]

subst-lemma _ _ _ (Num n) = refl

subst-lemma _ x _ (Var y)
  with x ≡? y
... | yes refl = refl
... | no _ = refl

subst-lemma g x ρ (Add e f adm-e adm-f)
  rewrite subst-lemma g x ρ adm-e |
          subst-lemma g x ρ adm-f
  = refl

subst-lemma g x ρ (Mul e f adm-e adm-f)
  rewrite subst-lemma g x ρ adm-e |
          subst-lemma g x ρ adm-f
  = refl

subst-lemma g x ρ (Let-1 e f adm-e)
  with subst-lemma g x ρ adm-e
... | ind =
  begin
    ⟦ Let x e f A[ x ↦ g ] ⟧ ρ
      ≡⟨ cong (λ C → ⟦ C ⟧ ρ) (subs-Let-1 x e) ⟩
    ⟦ Let x (e A[ x ↦ g ]) f ⟧ ρ
      ≡⟨⟩
    ⟦ f ⟧ ρ [ x ↦ ⟦ e A[ x ↦ g ] ⟧ ρ ]
      ≡⟨ cong (λ C → ⟦ f ⟧ ρ [ x ↦ C ]) ind ⟩
    ⟦ f ⟧ ρ [ x ↦ ⟦ e ⟧ ρ [ x ↦ ⟦ g ⟧ ρ ] ]
      ≡⟨ cong (λ C → ⟦ f ⟧ C) (sym (doubleupdate x)) ⟩
    ⟦ f ⟧ ρ [ x ↦ ⟦ g ⟧ ρ ] [ x ↦ ⟦ e ⟧ ρ [ x ↦ ⟦ g ⟧ ρ ] ]
      ≡⟨⟩
    ⟦ Let x e f ⟧ ρ [ x ↦ ⟦ g ⟧ ρ ]
  ∎

subst-lemma g x ρ (Let-2 e f x≢y xNFf adm-e) = {!   !}

subst-lemma g x ρ (Let-3 e f x≢y yNFg adm-e adm-f) = {!   !}

-- subst-lemma ($ n) = refl

-- subst-lemma {x} (` y)
--   with x ≡? y
-- ... | yes refl = refl
-- ... | no _ = refl

-- subst-lemma {x} {g} {ρ} (e + f)
--   rewrite subst-lemma {x} {g} {ρ} e |
--           subst-lemma {x} {g} {ρ} f = refl

-- subst-lemma {x} {g} {ρ} (e · f)
--   rewrite subst-lemma {x} {g} {ρ} e |
--           subst-lemma {x} {g} {ρ} f = refl

-- subst-lemma {x} {g} {ρ} (Let y e f)
--   with x ≡? y
-- ... | yes refl = 
--   begin
--   ⟦ Let x (e A[ x ↦ g ]) f ⟧ ρ
--     ≡⟨⟩
--   ⟦ f ⟧ ρ [ x ↦ ⟦ e A[ x ↦ g ] ⟧ ρ ]
--     ≡⟨ cong (λ C → ⟦ f ⟧ ρ [ x ↦ C ]) (subst-lemma {x} {g} {ρ} e) ⟩
--   ⟦ f ⟧ ρ [ x ↦ ⟦ e ⟧ ρ′ ]
--     ≡⟨ cong (λ C → ⟦ f ⟧ C) (sym (doubleupdate x)) ⟩
--   ⟦ f ⟧ ρ′ [ x ↦ ⟦ e ⟧ ρ′ ]
--     ≡⟨⟩
--   ⟦ Let x e f ⟧ ρ′
--   ∎ where ρ′ = ρ [ x ↦ ⟦ g ⟧ ρ ]

-- ... | no x≢y
--   with y ∈? fv g
-- ... | no ¬y∈g =
--   begin
--   ⟦ Let y (e A[ x ↦ g ]) (f A[ x ↦ g ]) ⟧ ρ
--     ≡⟨⟩
--   ⟦ f A[ x ↦ g ] ⟧ ρ [ y ↦ ⟦ e A[ x ↦ g ] ⟧ ρ ]
--     ≡⟨ cong (λ C → ⟦ f A[ x ↦ g ] ⟧ ρ [ y ↦ C ]) (subst-lemma e) ⟩
--   ⟦ f A[ x ↦ g ] ⟧ ρ′′
--     ≡⟨ subst-lemma f ⟩
--   ⟦ f ⟧ ρ′′ [ x ↦ ⟦ g ⟧ ρ′′ ]
--     ≡⟨⟩
--   ⟦ f ⟧ ρ [ y ↦ ⟦ e ⟧ ρ′ ] [ x ↦ ⟦ g ⟧ ρ′′ ]
--     ≡⟨ sym (cong (λ C → ⟦ f ⟧ C) (update-comm _ _ _ _ _  x≢y))⟩
--   ⟦ f ⟧ ρ [ x ↦ ⟦ g ⟧ ρ′′ ] [ y ↦ ⟦ e ⟧ ρ′ ] 
--     ≡⟨ cong (λ C → ⟦ f ⟧ ρ [ x ↦ C ] [ y ↦ ⟦ e ⟧ ρ′ ]) eq ⟩
--   ⟦ f ⟧ ρ [ x ↦ ⟦ g ⟧ ρ ] [ y ↦ ⟦ e ⟧ ρ′ ]
--     ≡⟨⟩
--   ⟦ f ⟧ ρ′ [ y ↦ ⟦ e ⟧ ρ′ ]
--     ≡⟨⟩
--   ⟦ Let y e f ⟧ ρ′
--   ∎ where ρ′ = ρ [ x ↦ ⟦ g ⟧ ρ ]
--           ρ′′ = ρ [ y ↦ ⟦ e ⟧ ρ′ ]

--           ag : Agree ρ ρ′′ (fv g)
--           ag = Agree-update-~∈ ¬y∈g

--           eq : ⟦ g ⟧ ρ′′ ≡ ⟦ g ⟧ ρ
--           eq = fv-lemma ρ′′ ρ g (sym-Agree ag)

-- ... | yes y∈g = {!   !}

-- _≈_ : ∀ e f → Set
-- e ≈ f = ∀ g → {!   !}
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

  goal : suc (suc (suc (suc (suc (μ a₁ +ℕ μ b₁ +ℕ 4))))) ≤
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

  goal : suc (ones a +ℕ ones b +ℕ 1) ≤ suc (ones a +ℕ suc (ones b))
  goal rewrite have (ones a) (ones b) = refl-≤
```
