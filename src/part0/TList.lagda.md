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

fetchElem : ∀ {A : Set} {As : Set *} → TList As → A ∈ As → A
fetchElem (a , _) here = a
fetchElem (_ , as) (there A∈As) = fetchElem as A∈As

Funs : (As : Set *) (B : Set) → Set
Funs ε B = B
Funs (A ∷ As) B = A → Funs As B

infixl 7.2 _have_by_ _have_apply_at_ -- haveApplyAt

_have_by_ : ∀ {As : Set *} → TList As → (A : Set) → A → TList (A ∷ As)
as have A by a = a , as

_have_apply_at_ : ∀ {As Bs : Set *} → TList Bs → (B : Set) → Funs As B → X (map (λ A → A ∈ Bs) As) → TList (B ∷ Bs)
_have_apply_at_ {ε} {Bs} bs B b tt = b , bs
_have_apply_at_ {A ∷ ε} {Bs} bs B f A∈Bs = f (fetchElem bs A∈Bs) , bs
_have_apply_at_ {A ∷ As@(A' ∷ As')} {Bs} bs B f (A∈Bs , pr) = _have_apply_at_ {As} {Bs} bs B (f (fetchElem bs A∈Bs)) pr

infixl 7.1 _haveit haveit-syntax
_haveit : {A : Set} {As : Set *} → TList (A ∷ As) → A
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