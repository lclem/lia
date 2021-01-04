---
title: Well-founded induction
---

NOTE: This section is more advanced and will be moved to later parts.

TODO: Turn `WellFounded` into a typeclass.

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.WellFounded where
open import part0.List
open import Agda.Primitive
```

An element `a` is *accessible* if all smaller elements `b` are accessible too.

```
-- generalisation to arbitrary domain and binary relations

data Acc {ℓ m} {A : Set ℓ} (R : A → A → Set m) (a : A) : Set (ℓ ⊔ m) where
  acc : ∀[ b ] (R b a → Acc R b) → Acc R a

WellFounded : ∀ {ℓ m} {A : Set ℓ} (_≺_ : A → A → Set m) → Set (ℓ ⊔ m)
WellFounded _≺_ = ∀[ a ] Acc _≺_ a

<-wf : WellFounded _<_
<-wf zero = acc λ _ ()
<-wf (suc n) with <-wf n
... | acc f = acc g
    where
    g : ∀ m → m < suc n → Acc _<_ m
    g zero _ = <-wf zero
    g (suc m) (s≤s m<n) = acc λ o o≤m → f o (trans-≤ o≤m m<n)
```

```
-- prove it by w.f. induction on R!
mon-wf : ∀ {ℓ m n o} {A : Set ℓ} {B : Set m}
  (R : A → A → Set n)
  (S : B → B → Set o)
  (f : A → B) →
  WellFounded S →
  (∀ {a b} → R a b → S (f a) (f b)) →
  WellFounded R
mon-wf R S f wf-S R⊆S a = acc {!!}
```

## Lexicographic product

```
_×ₗₑₓ_ : {A : Set} {B : Set} →
  (A → A → Set) →
  (B → B → Set) →
  (A × B → A × B → Set)
(_≺A_ ×ₗₑₓ _≺B_) (a0 , b0) (a1 , b1) = a0 ≺A a1 ⊎ (a0 ≡ a1 × b0 ≺B b1)

lex-wf : {A : Set} {B : Set}
  {_≺A_ : A → A → Set}
  {_≺B_ : B → B → Set} →
  WellFounded _≺A_ →
  WellFounded _≺B_ →
  WellFounded (_≺A_ ×ₗₑₓ _≺B_) 
lex-wf = {!!}
```



## List inclusion is well-founded

NOTE: The following is about *well-founded induction*
and it will be moved to some later parts.

```
-- This is more advanced and will be moved to later parts

-- the number of distinct elements strictly decreases

wf-⊂ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} → WellFounded {A = A *} _⊂_
wf-⊂ = mon-wf _⊂_ _<_ (length ∘ support) <-wf ⊂-len-support

```
