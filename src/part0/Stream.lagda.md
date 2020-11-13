---
title: Streams
---

```
module part0.Stream where
open import Agda.Primitive
open import part0.nat
open import part0.eq
open import part0.list hiding (_≈_; head)
open import part0.logic

record _ω {ℓ} (A : Set ℓ) : Set ℓ where
  coinductive
  constructor _∷_
  field
    head : A
    tail : A ω

open _ω public

record _≈_ {ℓ} {A : Set ℓ} (xs ys : A ω) : Set ℓ where
  coinductive
  field
    head-≈ : head xs ≡ head ys
    tail-≈ : tail xs ≈ tail ys

infix 5 _∈ω_
data _∈ω_ {ℓ} {A : Set ℓ} : A → A ω → Set where
  here : ∀ {a} {as : A ω} → a ∈ω a ∷ as
  there : ∀ {a b} {as : A ω} → a ∈ω as → a ∈ω b ∷ as

-- infix 5 _∈ω_!_
-- data _∈ω_ {ℓ} {A : Set ℓ} : A → A ω → Set where
--   here : ∀ {a} {as : A ω} → a ∈ω a ∷ as
--   there : ∀ {a b} {as : A ω} → a ∈ω as → a ∈ω b ∷ as

_!_ : ∀ {ℓ} {A : Set ℓ} → A ω → ℕ → A
as ! zero = head as
as ! suc n = tail as ! n

infixl 9 _⊆ω_

_⊆ω_ : ∀ {ℓ} {A : Set ℓ} → A * → A ω → Set ℓ
xs ⊆ω ys = ∀[ x ] (x ∈ xs → x ∈ω ys)

forAllInω : ∀ {ℓ m} {A : Set ℓ} (B : A → A ω → Set m) → Set (ℓ ⊔ m)
forAllInω B = ∀[ a ] ∀[ as ] (a ∈ω as → B a as)

--infix 8 ∀[_∈ω_]_
--syntax forAllInω (λ a as → B) = ∀[ a ∈ω as ] B

scanω : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B → A) → A → B ω → A ω
head (scanω f a bs) = a
tail (scanω f a bs) = scanω f (f a (head bs)) (tail bs)

mapω : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B) → A ω → B ω
head (mapω f as) = f (head as)
tail (mapω f as) = mapω f (tail as)

zipWithω : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → (A → B → C) → A ω → B ω → C ω
head (zipWithω f as bs) = f (head as) (head bs)
tail (zipWithω f as bs) = zipWithω f (tail as) (tail bs)

takeω : ∀ {ℓ} {A : Set ℓ} → ℕ → A ω → A *
takeω zero _ = ε
takeω (suc n) as = head as ∷ takeω n (tail as)

dropω : ∀ {ℓ} {A : Set ℓ} → ℕ → A ω → A ω
dropω zero as = as
dropω (suc n) as = dropω n (tail as)

{-# TERMINATING #-}
nats : ℕ ω
head nats = 0
tail nats = mapω suc nats

zeroes ones : ℕ ω
head zeroes = 0
tail zeroes = zeroes

head ones = 1
tail ones = ones

nats' : ℕ ω
nats' = scanω _+_ 0 ones

{-# TERMINATING #-}
fibs : ℕ ω
head fibs = 0
head (tail fibs) = 1
tail (tail fibs) = zipWithω _+_ fibs (tail fibs)



-- scan2ω : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → A → B → A) → A → A → B ω → A ω
-- head (scan2ω f a1 a2 bs) = a1
-- head (tail (scan2ω f a1 a2 bs)) = a2
-- tail (tail (scan2ω f a1 a2 bs)) = scan2ω f a2 (f a1 a2 (head bs)) (tail bs)

-- fibs' : ℕ ω
-- fibs' = scan2ω (λ a b c → a + b) 0 1 zeroes


```
