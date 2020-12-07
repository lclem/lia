---
title: "TLists 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.TList where
open import part0.List public

X_ : ∀ {ℓ} → Set ℓ * → Set ℓ
X ε = T
X (A ∷ ε) = A
X (A ∷ As@(_ ∷ _)) = A × X As

data TList {ℓ} : Set ℓ * → Set ℓ where
    BEGIN : TList ε
    _,_ : ∀ {A : Set ℓ} {As : Set ℓ *} → A → TList As → TList (A ∷ As)

fetchElem : ∀ {ℓ} {A : Set ℓ} {As : Set ℓ *} → TList As → A ∈ As → A
fetchElem (a , _) here = a
fetchElem (_ , as) (there A∈As) = fetchElem as A∈As

Funs : ∀ {ℓ} (As : Set ℓ *) (B : Set ℓ) → Set ℓ
Funs ε B = B
Funs (A ∷ As) B = A → Funs As B

infixl 7.2 _have_by_ _have_apply_at_ -- haveApplyAt

_have_by_ : ∀ {ℓ} {As : Set ℓ *} → TList As → (A : Set ℓ) → A → TList (A ∷ As)
as have A by a = a , as

_have_apply_at_ : ∀ {ℓ} {As Bs : Set ℓ *} → TList Bs → (B : Set ℓ) → Funs As B → X (map (λ A → A ∈ Bs) As) → TList (B ∷ Bs)
_have_apply_at_ {ℓ} {ε} {Bs} bs B b tt = b , bs
_have_apply_at_ {ℓ} {A ∷ ε} {Bs} bs B f A∈Bs = f (fetchElem bs A∈Bs) , bs
_have_apply_at_ {ℓ} {A ∷ As@(A' ∷ As')} {Bs} bs B f (A∈Bs , pr) = _have_apply_at_ {ℓ} {As} {Bs} bs B (f (fetchElem bs A∈Bs)) pr

infixl 7.1 _haveit haveit-syntax
_haveit : ∀ {ℓ} {A : Set ℓ} {As : Set ℓ *} → TList (A ∷ As) → A
(a , _) haveit = a

haveit-syntax = _haveit
syntax haveit-syntax x = x END

_ : BEGIN
    have ℕ apply 2 at tt
    have ℕ apply suc at here
    have ℕ apply _+_ at here , there here
    have ℕ apply _+_ at here , there here
    ≡ 8 , 5 , 3 , 2 , BEGIN
_ = refl

backType : ∀ {ℓ} {A : Set ℓ} → A * → ℕ → Set ℓ
backType {A = A} as 0 = ∀ {x} {xs : A *} → x ∈ (as ++ x ∷ xs)
backType as (suc n) = ∀ {a} → backType (a ∷ as) n

back : ∀ {ℓ} {A : Set ℓ} (n : ℕ) → backType ε n
back {A = A} n = go ε n where

  go : (as : A *) → (n : ℕ) → backType as n
  go ε zero = here
  go (_ ∷ as) zero
    with go as zero
  ... | ind = there ind
  go as (suc n) {a} = go (a ∷ as) n

_ : BEGIN
    have ℕ apply 2 at tt
    have ℕ apply suc at back 0
    have ℕ apply _+_ at back 0 , back 1
    have ℕ apply _+_ at back 0 , back 1
    ≡ 8 , 5 , 3 , 2 , BEGIN
_ = refl
```

```
-- Funs As B → X (map (λ A → A ∈ Bs) As) 
_have_by-magic : ∀ {As Bs : Set *} → TList Bs → (B : Set) → TList (B ∷ Bs)
bs have B by-magic = bs have B apply _ at _
```

```
-- tmap : ∀ {ℓ} {As Bs : Vector (Set ℓ) n} → TVector {ℓ} {n} (zipWith Fun As Bs) → TList As → TList Bs
-- tmap {ε} {ε} ε ε = ε
-- tmap {A ∷ As} {B ∷ Bs} (f ∷ fs) (a ∷ as) = f a ∷ tmap fs as

-- tfilter :

-- dependent map over a list
-- dmap : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} → Π A B → (as : A *) → TList (map B as)
-- dmap _ ε = BEGIN
-- dmap f (a ∷ as) = f a ∷ dmap f as

-- filter-proof : ∀ {A : Set} {P : A → Set} → (P? : Decidable P) → (as : A *) → TList {! map (Dec ∘ P) as  !}
-- filter-proof {A} {P} P? as = {!   !} where
--
--   as? : TList (map (Dec ∘ P) as)
--   as? = dmap P? as
```