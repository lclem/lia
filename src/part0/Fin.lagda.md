---
title: Natural numbers
---

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.Fin where
open import part0.nat
open import part0.eq
open import part0.decidable
open import part0.logic

data Fin : ℕ → Set where
    fzero : {n : ℕ} → Fin (suc n)
    fsuc : {n : ℕ} → Fin n → Fin (suc n)

inj-fsuc : ∀ {n} {i j : Fin n} → fsuc i ≡ fsuc j → i ≡ j
inj-fsuc refl = refl

_≟Fin_ : ∀ {n} → Decidable2 (_≡_ {A = Fin n})
fzero ≟Fin fzero = yes {proof = refl}
fzero ≟Fin fsuc _ = no {proof = λ ()}
fsuc _ ≟Fin fzero = no {proof = λ ()}
fsuc x ≟Fin fsuc y with x ≟Fin y
... | yes {refl} = yes {proof = refl}
... | no {x≢y} = no {proof = λ{ refl → x≢x-elim x≢y}}

instance
  eqFin : ∀ {n} → Eq (Fin n)
  _≡?_ {{eqFin}} = _≟Fin_
```

If a proposition is pointwise decidable, then it is decidable on the interval.
```
Fin-Dec : ∀ {ℓ n} {P : Fin n → Set ℓ} → ∀[ k ] Dec (P k) → Dec (∃[ k ] P k)
Fin-Dec {n = zero} P? = no {proof = λ{()}}
Fin-Dec {n = suc n} P? with P? fzero
... | yes {yes-fzero} = yes {proof = fzero , yes-fzero}
... | no {proof = no-fzero} with Fin-Dec {n = n} λ k → P? (fsuc k)
... | yes {proof = k , yes-fsuc} =  yes {proof = fsuc k , yes-fsuc}
... | no {proof = no-fsuc} = no {proof = λ{(fzero , Pk) → no-fzero Pk; (fsuc k , Pk) → no-fsuc (k , Pk)}}
```

```
Fin2ℕ : ∀ {n} → Fin n → ℕ
Fin2ℕ fzero = zero
Fin2ℕ (fsuc i) = suc (Fin2ℕ i)

-- returns the largest possible element
ℕ2Fin : ∀ (n : ℕ) → Fin (suc n)
ℕ2Fin zero = fzero
ℕ2Fin (suc n) = fsuc (ℕ2Fin n)

fzero≢fsuc : ∀ {n : ℕ} {k} → fzero {n} ≢ fsuc k
fzero≢fsuc ()

Fin-monotone : ∀ {m n} → m ≤ n → Fin m → Fin n
Fin-monotone {suc m} {suc n} (s≤s m≤n) fzero = fzero
Fin-monotone (s≤s m≤n) (fsuc k) = fsuc (Fin-monotone m≤n k)

fadd : ∀ {n} (m : ℕ) (k : Fin n) → Fin (m + n)
fadd zero k = k
fadd (suc m) k = fsuc (fadd m k)

Fin-add-≢ : ∀ {m n} (i : Fin m) (j : Fin n) → Fin-monotone ≤+ i ≢ fadd m j
Fin-add-≢ {zero} ()
Fin-add-≢ {suc m} {n} (fsuc i) j eqv = Fin-add-≢ {m} {n} i j (inj-fsuc eqv)

```



