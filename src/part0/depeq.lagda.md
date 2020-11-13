---
title: Dependent equality
---

This section is definitely advanced and will be moved  beyond part 0.

```
module part0.depeq where
open import part0.eq public

-- dependent equality
_≡[_]_ : ∀ {ℓ m} {X : Set ℓ} {A : X → Set m} {x y : X} → A x → x ≡ y → A y → Set
b ≡[ refl ] c = b ≡ c

-- only the input uses dependent equality
-- can be generalised to the output too
dcong : ∀ {ℓ m n} {X : Set ℓ} {A : X → Set m} {B : Set n} {x y : X} (f : {x : X} → A x → B) {ax : A x} {ay : A y} (x≡y : x ≡ y) → ax ≡[ x≡y ] ay → f ax ≡ f ay
dcong f refl refl = refl

dcong' : ∀ {ℓ m n} {X : Set ℓ} {A : X → Set m} {B : X → Set n} {x y : X} (f : {x : X} → A x → B x) {ax : A x} {ay : A y} (x≡y : x ≡ y) → ax ≡[ x≡y ] ay → f ax ≡[ x≡y ] f ay
dcong' f refl refl = refl

dcong'' : ∀ {ℓ m n} {X : Set ℓ} {A : X → Set m} {B : X → Set n} {x y : X} (g : X → X) (f : {x : X} → A x → B (g x)) {ax : A x} {ay : A y} →
  (x≡y : x ≡ y) →
  ax ≡[ x≡y ] ay →
  _≡[_]_ {A = B} {x = g x} {y = g y} (f {x} ax) (cong g {x} {y} x≡y) (f {y} ay)
dcong'' g f refl refl = refl

dcong-cong : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {a1 a2 : A} (f : (a : A) → B a) (a1≡a2 : a1 ≡ a2) → f a1 ≡[ a1≡a2 ] f a2
dcong-cong f refl = refl

dcong2 : ∀ {ℓ m n} {A : Set ℓ} {B : A → Set m} {C : Set n} (f : (a : A) → B a → C) {x y : A} {zx : B x} {ty : B y} → (x≡y : x ≡ y) → zx ≡[ x≡y ] ty → f x zx ≡ f y ty
dcong2 f refl refl = refl

_≡2[_,_]_ : ∀ {ℓ m n} {X : Set ℓ} {A : X → Set n} {B : (x : X) → A x → Set m} {x y : X} {ax : A x} {ay : A y} →
  B x ax →
  (x≡y : x ≡ y) →
  (ax ≡[ x≡y ] ay) →
  B y ay → Set
b ≡2[ refl , refl ] c = b ≡ c

ddcong : ∀ {ℓ m n} {X : Set ℓ} {A : X → Set m} {B : (x : X) → A x → Set n} {x y : X} (f : {x : X} → (ax : A x) → B x ax) {ax : A x} {ay : A y} (x≡y : x ≡ y) → (ax≡ay : ax ≡[ x≡y ] ay) → f ax ≡2[ x≡y , ax≡ay ] f ay
ddcong f refl refl = refl
```
