---
title: Utilities 🚧
---
  
```
module part0.Utils where
open import Agda.Primitive public

private
  variable
    ℓ : Level
    A : Set ℓ

whatever : Setω
whatever = ∀ {ℓ} {A : Set ℓ} → A

Fn : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
Fn A B = A → B

const : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → B → A → B
const b _ = b

id : ∀ {ℓ} {A : Set ℓ} → A → A
id x = x

apply : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} → (f : ((a : A) → B a)) → (a : A) → B a
apply f a = f a

infixr 12 _∘_

-- function application
infixr 100 _$_
_$_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B) → A → B
f $ x = f x

DFn : ∀ {ℓ m} → (A : Set ℓ) → (B : A → Set m) → Set (ℓ ⊔ m)
DFn A B = (a : A) → B a

-- dependent composition
_∘_ : ∀ {ℓ m o} {A : Set ℓ} {B : A → Set m} {C : A → Set o} →
  (f : {a : A} → B a → C a) → (g : (a : A) → B a) → (a : A) → C a
(f ∘ g) x = f (g x)

-- composition with the arguments swapped
_﹔_ : ∀ {ℓ m o} {A : Set ℓ} {B : Set m} {C : Set o} →  (A → B) → (B → C) → A → C
f ﹔ g = g ∘ f

-- guess the argument!
auto : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} → ((a : A) → B a) → {a : A} → B a
auto f {a} = f a

inst-auto : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} → ((a : A) → B a) → {{a : A}} → B a
inst-auto f {{a}} = f a

by-inst : ∀ {a} {A : Set a} → {{A}} → A -- {{_ : A}} → A
by-inst {{x}} = x
```
