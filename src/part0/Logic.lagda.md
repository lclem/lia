---
title: The logic of Agda🚧
---

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.Logic where
open import part0.Utils public

Π : ∀ {ℓ m} (A : Set ℓ) → (B : A → Set m) → Set (ℓ ⊔ m)
Π A B = (a : A) → B a

forAll : ∀ {ℓ m} {A : Set ℓ} → (B : A → Set m) → Set (ℓ ⊔ m)
forAll {A = A} B = Π A B

infixr 10 _,_
record Σ {ℓ m} (A : Set ℓ) (B : A → Set m) : Set (ℓ ⊔ m) where
    constructor _,_
    field
      dfst : A
      dsnd : B dfst

open Σ public

thereExists : ∀ {ℓ m} {A : Set ℓ} (B : A → Set m) → Set (ℓ ⊔ m)
thereExists {A = A} B = Σ A B

-- We make the first component implicit, since it can often be recovered from the second one
infix 10 [[_]]
record Σ' {ℓ m} (A : Set ℓ) (B : A → Set m) : Set (ℓ ⊔ m) where
  constructor [[_]]
  field
    {dfst} : A
    dsnd : B dfst

open Σ' public

thereExists' : ∀ {ℓ m} {A : Set ℓ} (B : A → Set m) → Set (ℓ ⊔ m)
thereExists' {A = A} B = Σ' A B

infix 0 forAll thereExists thereExists'
syntax forAll (λ x → B) = ∀[ x ] B
syntax thereExists (λ x → B) = ∃[ x ] B
syntax thereExists' (λ x → B) = ∃[[ x ]] B

infixr 2 _×_
-- _×_ : ∀ {ℓ m} (A : Set ℓ) (B : Set m) → Set (ℓ ⊔ m)
-- A × B = Σ A (λ _ → B)

record _×_ {ℓ m} (A : Set ℓ) (B : Set m) : Set (ℓ ⊔ m) where
  constructor _,_
  field
    fst : A
    snd : B

open _×_ public

-- tensor product of two functions
infixr 11 _⊗_
_⊗_ : ∀ {ℓ m n o} {A : Set ℓ} {B : Set m} {C : Set n} {D : Set o} → (A → C) → (B → D) → A × B → C × D
(f ⊗ g) (a , b) = f a , g b

-- fst : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → A × B → A
-- fst (a , _) = a
--
-- snd : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → A × B → B
-- snd (_ , b) = b

data T {ℓ} : Set ℓ where
    tt : T

data F : Set where

F-elim : ∀ {ℓ} {A : Set ℓ} → F → A
F-elim ()

infix 100 ~_
~_ : ∀ {ℓ} → Set ℓ → Set ℓ
~ x = x → F

~~-intro : ∀ {ℓ} {A : Set ℓ} → A → ~ ~ A
~~-intro x f = f x

infixr 1 _⊎_

data _⊎_ {ℓ m} (A : Set ℓ) (B : Set m) : Set (ℓ ⊔ m) where
    left : A → A ⊎ B
    right : B → A ⊎ B

case : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case f g (left x) = f x
case f g (right x) = g x

-- we need the law of excluded middle to define the semantics of first-order logic in a classical way
LEM-Type : Setω
LEM-Type = ∀ {ℓ} {A : Set ℓ} → A ⊎ ~ A

-- postulate LEM : LEM-Type

~~-Lemma : ∀ {ℓ} {A : Set ℓ} → ~ ~ A → A
~~-Lemma = {!   !}

-- LEM needed here
~→-Lemma1 : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (~ B → ~ A) → A → B
~→-Lemma1 = {!   !}

-- without LEM
~→-Lemma2 contr : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B) → ~ B → ~ A
~→-Lemma2 = {!   !}
contr = {!!}

infixr 0 _↔_
_↔_ : ∀ {ℓ m} (A : Set ℓ) (B : Set m) → Set (ℓ ⊔ m)
A ↔ B = (A → B) × (B → A)

refl-↔ : ∀ {ℓ} {A : Set ℓ} → A ↔ A
refl-↔ = id , id

trans-↔ : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → A ↔ B → B ↔ C → A ↔ C
trans-↔ A↔B B↔C = (λ A → fst B↔C (fst A↔B A)) , (λ C → snd A↔B (snd B↔C C))

-- cong-↔ : ∀ {ℓ m} {A B : Set ℓ} (f : Set ℓ → Set m) → A ↔ B → f A ↔ f B
-- cong-↔ f (A→B , B→A) = (λ fA → {!   !} ) , {!   !}

-- equivalence reasoning
infix  1 ↔begin_
infixr 2 _↔⟨⟩_ _↔⟨_⟩_
infix  3 _↔∎

↔begin_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → A ↔ B → A ↔ B
↔begin A↔B = A↔B

_↔⟨⟩_ : ∀ {ℓ m} (A : Set ℓ) {B : Set m} → A ↔ B → A ↔ B
A ↔⟨⟩ A↔B = A↔B

_↔⟨_⟩_ : ∀ {ℓ m n} (A : Set ℓ) {B : Set m} {C : Set n} → A ↔ B → B ↔ C → A ↔ C
A ↔⟨ A↔B ⟩ B↔C = trans-↔ A↔B B↔C

_↔∎ : ∀ {ℓ} (A : Set ℓ) → A ↔ A
A ↔∎ = refl-↔
```

## Random examples

```
--rnd1 : ∀ (P : Set) → ~ ~ (P ⊎ ~ P)
--rnd1 P x = x (right (λ x → x₁ (left x)))

rnd2 : ∀ (P Q : Set) → ~ ~ P → ~ ~ Q → ~ ~ (P × Q)
rnd2 P Q ~~P ~~Q ~[P×Q] = {!!}
```
