---
title: Natural numbers
---

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.nat where
open import part0.utils
open import part0.eq
open import part0.decidable
open import part0.logic

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

_≟ℕ_ : Decidable2 (_≡_ {A = ℕ})
zero ≟ℕ zero  = yes {proof = refl}
zero ≟ℕ suc _ = no {proof = λ ()}
suc x ≟ℕ zero = no {proof = λ ()}
suc x ≟ℕ suc y with x ≟ℕ y
... | yes {refl} = yes {proof = refl}
... | no {x≢y} = no {proof = λ sucx≡sucy → x≢y (suc-inj sucx≡sucy)}

instance
  eqℕ : Eq ℕ
  _≡?_ {{eqℕ}} = _≟ℕ_

infix 5 _≤_ _<_ _≥_ _>_

data _≤_ : ℕ → ℕ → Set where
  0≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n
```

Examples:

```
1≤2 : 1 ≤ 2
1≤2 = {!!}

```

```
postulate n≤n : ∀ (n : ℕ) → n ≤ n
postulate refl-≤ : ∀ {n : ℕ} → n ≤ n

suc-≤ : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
suc-≤ (s≤s p) = p

-- TODO
postulate _≤?_ : ∀ (m n : ℕ) → Dec (m ≤ n)

max : ℕ → ℕ → ℕ
max m n with m ≤? n
... | yes = n
... | no = m

_≥_ _<_ _>_ : ℕ → ℕ → Set
m ≥ n = n ≤ m
m < n = suc m ≤ n
m > n = n < m

postulate _<?_ : ∀ (m n : ℕ) → Dec (m < n)

suc-> : ∀ {m n : ℕ} → suc m > suc n → m > n
suc-> (s≤s p) = p

n<sucn : ∀ {n} → n < suc n
n<sucn {zero} = s≤s 0≤n
n<sucn {suc n} = s≤s n<sucn

n≤sucn : ∀ {n} → n ≤ suc n
n≤sucn {zero} = 0≤n
n≤sucn {suc n} = s≤s n≤sucn

postulate n≤sucsucn : ∀ {n} → n ≤ suc (suc n)

suc-< : ∀ {m n : ℕ} → suc m < suc n → m < n
suc-< = suc-≤

postulate ¬≤→> : ∀ {m n} → ¬ (m ≤ n) → n < m
postulate ¬<→≥ : ∀ {m n} → ¬ (m < n) → m ≥ n
postulate <→≤ : ∀ {m n} → m < n → m ≤ n

trans-≤ : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
trans-≤ 0≤n _ = 0≤n
trans-≤ (s≤s l≤m) (s≤s m≤n) = s≤s (trans-≤ l≤m m≤n)

postulate <trans-≤ : ∀ {l m n} → l < m → m ≤ n → l < n
postulate ≤trans-< : ∀ {l m n} → l ≤ m → m < n → l < n
postulate trans-< : ∀ {l m n} → l < m → m < n → l < n
postulate trans-> : ∀ {l m n} → l > m → m > n → l > n

antisym-≤ : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
antisym-≤ = {!!}

n<suc2n : ∀ {n} → n < suc (suc n)
n<suc2n {n} = trans-< (n<sucn {n}) (n<sucn {suc n})

<→≢ : ∀ {m n} → m < n → m ≢ n
<→≢ (s≤s 0≤n) ()
<→≢ (s≤s (s≤s m<n)) equiv = <→≢ (s≤s m<n) (suc-inj equiv) 

trichotomy-< : ∀ {m n} → m < n ∨ m ≡ n ∨ m > n
trichotomy-< = {!!}

≤∧≢→< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤∧≢→< = {!!}

infix  1 begin≤_ begin<_
infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≤≡⟨_⟩_ _<→≤⟨⟩_ _<≤⟨_⟩_ _≤<⟨_⟩_ _<⟨_⟩_ _<⟨⟩_  -- _<≤⟨⟩_
infix  3 _end≤ _∎≤ _end< _∎<

begin≤_ : {x y : ℕ} → x ≤ y → x ≤ y
begin≤ p = p

begin<_ : {x y : ℕ} → x < y → x < y
begin< p = p

_≤⟨⟩_ : (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
_ ≤⟨⟩ p = p

_<⟨⟩_ : (x : ℕ) {y : ℕ} → x < y → x < y
_ <⟨⟩ p = p

_<→≤⟨⟩_ : (x : ℕ) {y : ℕ} → x < y → x ≤ y
_ <→≤⟨⟩ p = <→≤ p

_≤⟨_⟩_ : (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
_ ≤⟨ x≤y ⟩ y≤z = trans-≤ x≤y y≤z

_<⟨_⟩_ : (x : ℕ) {y z : ℕ} → x < y → y < z → x < z
_ <⟨ x<y ⟩ y<z = trans-< x<y y<z

--_<≤⟨⟩_ : (x : ℕ) {y z : ℕ} → x < y → y ≤ z → x < z
--_ <≤⟨⟩ y≤z = <trans-≤ x<y y≤z

_<≤⟨_⟩_ : (x : ℕ) {y z : ℕ} → x < y → y ≤ z → x < z
_ <≤⟨ x<y ⟩ y≤z = <trans-≤ x<y y≤z

_≤<⟨_⟩_ : (x : ℕ) {y z : ℕ} → x ≤ y → y < z → x < z
_ ≤<⟨ x≤y ⟩ y<z = ≤trans-< x≤y y<z

_≤≡⟨_⟩_ : (x : ℕ) {y z : ℕ} → x ≡ y → y ≤ z → x ≤ z
_≤≡⟨_⟩_ x {y} {z} x≡y y≤z = subst (_≤ z) (sym x≡y) y≤z

_end≤ _∎≤ : (x : ℕ) → x ≤ x
_ end≤ = refl-≤
_ ∎≤ = refl-≤

_end< _∎< : (x : ℕ) → x ≤ x
_ end< = refl-≤
_ ∎< = refl-≤

test : (x0 x y z : ℕ) → x0 ≤ x → x ≤ y → y < z → x0 < z
test x0 x y z p0 p q =
  begin<
    x0 ≤<⟨ p0 ⟩
    x ≤<⟨ p ⟩
    y <≤⟨ q ⟩
    z
  end<

¬n<n : ∀ {n} → ¬ (n < n)
¬n<n {zero} = λ ()
¬n<n {suc n} q with ¬n<n {n}
... | p = p (suc-≤ q)

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

-- check that the definition above is equivalent to the built-in one
-- {-# BUILTIN NATPLUS _+_ #-}

-- usually the first two arguments are required...
postulate assoc-+ : {l m n : ℕ} → l + m + n ≡ l + (m + n)
postulate n+0≡n : {n : ℕ} → n + zero ≡ n
postulate sucm+n≡m+sucn : {m n : ℕ} → suc m + n ≡ m + suc n
postulate suc-lemma : {m n : ℕ} → m + suc n ≡ suc m + n -- the commuting variant of the above
-- lemma-plus-zero = ?

≤+ : ∀ {m n} → m ≤ m + n
≤+ {zero} {n} = 0≤n
≤+ {suc m} {n} = s≤s ≤+

infixl 7 _*_

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + n * m

-- {-# BUILTIN NATTIMES _*_ #-}
```

Examples (these will be useful thorough the book)

```
1≤2*1 : 1 ≤ 2 * 1
1≤2*1 = {!!}
```

```
postulate n*1≡n : ∀ {n} → n * suc zero ≡ n
-- usually needs the first two arguments
postulate assocLeft-+* : ∀ {a b c} → a * b + a * c ≡ a * (b + c)
postulate cong-*< : ∀ {a b c} → a ≥ zero → b < c → a * b < a * c
-- postulate cong-< : ∀ {a b c} → a ≥ 0 → b < c → a * b < a * c

postulate comm-+ : ∀ {m n} → m + n ≡ n + m

-- monus

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n
```

## Arithmetic expressions

```

data AExp : Set where
  Num : ℕ → AExp
  Suc : AExp → AExp
  _+E_ : AExp → AExp → AExp
  _*E_ : AExp → AExp → AExp

A⟦_⟧ : AExp → ℕ
A⟦ Num n ⟧ = n
A⟦ Suc n ⟧ = suc (A⟦ n ⟧)
A⟦ e +E f ⟧ = A⟦ e ⟧ + A⟦ f ⟧
A⟦ e *E f ⟧ = A⟦ e ⟧ * A⟦ f ⟧
```

## Arithmetic contexts

```
infixl 20 _+C_
infixl 25 _*C_

data ACtx : Set where
  □ : ACtx
  Num : ℕ → ACtx
  Suc : ACtx → ACtx
  _+C_ : ACtx → ACtx → ACtx
  _*C_ : ACtx → ACtx → ACtx

-- replace the hole with a given formula
aCtxApply : ACtx → AExp → AExp
aCtxApply □ e = e
aCtxApply (Num n) _ = Num n
aCtxApply (Suc ctx) e = Suc (aCtxApply ctx e)
aCtxApply (ctx1 +C ctx2) e = aCtxApply ctx1 e +E aCtxApply ctx2 e
aCtxApply (ctx1 *C ctx2) e = aCtxApply ctx1 e *E aCtxApply ctx2 e

postulate cong-< : ∀ {a b} → (ctx : ACtx) → a < b → A⟦ aCtxApply ctx (Num a) ⟧ < A⟦ aCtxApply ctx (Num b) ⟧
postulate cong-≤ : ∀ {a b} → (ctx : ACtx) → a ≤ b → A⟦ aCtxApply ctx (Num a) ⟧ ≤ A⟦ aCtxApply ctx (Num b) ⟧

longAnd : ∀ {ℓ} → Set ℓ → ℕ → Set ℓ
longAnd _ zero = ⊤
longAnd A (suc zero) = A
longAnd A (suc (suc n)) = A ∧ longAnd A (suc n)
```
