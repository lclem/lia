---
title: Natural numbers🚧
---

```
{-# OPTIONS --rewriting --confluence-check #-}
{-# OPTIONS --allow-unsolved-metas #-}

module part0.Naturals where
open import part0.Equality public

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

private
  variable
    k m n : ℕ

suc-inj : ∀ {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

_≟ℕ_ : Decidable2 (_≡_ {A = ℕ})
zero ≟ℕ zero  = yes refl
zero ≟ℕ suc _ = no (λ ())
suc x ≟ℕ zero = no (λ ())
suc x ≟ℕ suc y with x ≟ℕ y
... | yes refl = yes refl
... | no x≢y = no (λ sucx≡sucy → x≢y (suc-inj sucx≡sucy))

instance
  eqℕ : Eq ℕ
  _≡?_ {{eqℕ}} = _≟ℕ_

infix 5 _≤_ _<_ _≥_ _>_

data _≤_ : ℕ → ℕ → Set where
  instance 0≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : m ≤ n → suc m ≤ suc n

instance inst-s≤s : {{m ≤ n}} → suc m ≤ suc n
inst-s≤s {{arg}} = s≤s arg
```

```
postulate n≤n : ∀ (n : ℕ) → n ≤ n

refl-≤ : n ≤ n
refl-≤ {zero} = 0≤n
refl-≤ {suc n} = s≤s refl-≤

suc-≤ : ∀ {m n : ℕ} → suc m ≤ suc n → m ≤ n
suc-≤ (s≤s p) = p

-- TODO
_≤?_ : ∀ m n → Dec (m ≤ n)
zero ≤? n = yes 0≤n
suc m ≤? zero = no λ ()
suc m ≤? suc n
  with m ≤? n
... | yes m≤n = yes (s≤s m≤n)
... | no ~m≤n = no λ{ (s≤s m≤n) → ~m≤n m≤n}

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

postulate m≤n→m≤sucn : ∀ {m n} → m ≤ n → m ≤ suc n
postulate n≤sucsucn : ∀ {n} → n ≤ suc (suc n)

suc-< : ∀ {m n : ℕ} → suc m < suc n → m < n
suc-< = suc-≤

postulate ~≤→> : ∀ {m n} → ~ (m ≤ n) → n < m
postulate ~<→≥ : ∀ {m n} → ~ (m < n) → m ≥ n
postulate <→≤ : ∀ {m n} → m < n → m ≤ n

trans-≤ : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
trans-≤ 0≤n _ = 0≤n
trans-≤ (s≤s l≤m) (s≤s m≤n) = s≤s (trans-≤ l≤m m≤n)

_ : 1 ≤ 2
_ = by-inst

-- instance inst-trans-≤ : ∀ {l m n} → {{l ≤ m}} → {{m ≤ n}} → l ≤ n
-- inst-trans-≤ {{arg1}} {{arg2}} = trans-≤ arg1 arg2

postulate <trans-≤ : ∀ {l m n} → l < m → m ≤ n → l < n
postulate ≤trans-< : ∀ {l m n} → l ≤ m → m < n → l < n
postulate trans-< : ∀ {l m n} → l < m → m < n → l < n
postulate trans-> : ∀ {l m n} → l > m → m > n → l > n

antisym-≤ : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
antisym-≤ = {!!}

max : ℕ → ℕ → ℕ
max m n with m ≤? n
... | yes _ = n
... | no _ = m

max-zero-left : ∀ m → max 0 m ≡ m
max-zero-left _ = refl

max-zero-right : ∀ m → max m 0 ≡ m
max-zero-right zero = refl
max-zero-right (suc m) = refl

-- {-# REWRITE  #-}

-- instance
max-prop-left : m ≤ max m n 
max-prop-left {m} {n}
  with m ≤? n
... | yes m≤n = m≤n
... | (no _) = refl-≤

-- instance
sym-max : max m n ≡ max n m
sym-max = {!   !}

max-≤-left : max k m ≤ n → k ≤ n
max-≤-left {k} {m} {n} maxkm≤n
  with k ≤? m
... | yes k≤m = trans-≤ k≤m maxkm≤n
... | no _ = maxkm≤n

max-≤-right : max k m ≤ n → m ≤ n
max-≤-right {k} {m} {n} maxkm≤n rewrite sym-max {k} {m} = max-≤-left maxkm≤n

-- instance
inst-max-≤-left : {{max k m ≤ n}} → k ≤ n
inst-max-≤-left {{arg}} = max-≤-left arg

-- instance
inst-max-≤-right : {{max k m ≤ n}} → m ≤ n
inst-max-≤-right {{arg}} = max-≤-right arg

_ : max m n ≤ m
_ = {!   !}

n<suc2n : ∀ {n} → n < suc (suc n)
n<suc2n {n} = trans-< (n<sucn {n}) (n<sucn {suc n})

<→≢ : ∀ {m n} → m < n → m ≢ n
<→≢ (s≤s 0≤n) ()
<→≢ (s≤s (s≤s m<n)) equiv = <→≢ (s≤s m<n) (suc-inj equiv) 

trichotomy-< : ∀ {m n} → m < n ⊎ m ≡ n ⊎ m > n
trichotomy-< = {!!}

≤×≢→< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤×≢→< = {!!}

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

~n<n : ∀ {n} → ~ (n < n)
~n<n {zero} = λ ()
~n<n {suc n} q with ~n<n {n}
... | p = p (suc-≤ q)

infixl 11 _+_

_+_ : ℕ → ℕ → ℕ
zero + m = m
suc n + m = suc (n + m)

-- check that the definition above is equivalent to the built-in one
-- {-# BUILTIN NATPLUS _+_ #-}

-- usually the first two arguments are required...
postulate assoc-+ : {l m n : ℕ} → l + m + n ≡ l + (m + n)

n+0≡n : ∀ n → n + zero ≡ n
n+0≡n zero = refl
n+0≡n (suc n) rewrite n+0≡n n = refl

{-# REWRITE n+0≡n #-}

postulate sucm+n≡m+sucn : {m n : ℕ} → suc m + n ≡ m + suc n
postulate suc-lemma : {m n : ℕ} → m + suc n ≡ suc m + n -- the commuting variant of the above

≤+ : ∀ {m n} → m ≤ m + n
≤+ {zero} {n} = 0≤n
≤+ {suc m} {n} = s≤s (≤+ {m} {n})

infixl 12 _*_

_*_ : ℕ → ℕ → ℕ
zero * m = zero
suc n * m = m + n * m

-- {-# BUILTIN NATTIMES _*_ #-}
```

Examples (these will be useful thorough the book)

```
1≤2*1 : 1 ≤ 2 * 1
1≤2*1 = by-inst
```

```
postulate n*1≡n : ∀ n → n * 1 ≡ n

-- usually needs the first two arguments
postulate assocLeft-+* : ∀ {a b c} → a * b + a * c ≡ a * (b + c)
postulate cong-*< : ∀ {a b c} → a ≥ zero → b < c → a * b < a * c
-- postulate cong-< : ∀ {a b c} → a ≥ 0 → b < c → a * b < a * c

postulate comm-+ : ∀ {m n} → m + n ≡ n + m

{-# REWRITE n*1≡n  #-}

m≤1+n→~m≤n→m≡1+n : m ≤ 1 + n → ~ (m ≤ n) → m ≡ 1 + n
m≤1+n→~m≤n→m≡1+n = ?

m≤1+n→~m≡1+n→m≤n : m ≤ 1 + n → ~ (m ≡ 1 + n) → m ≤ n
m≤1+n→~m≡1+n→m≤n = ?

-- monus
infixl 11 _∸_

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

sucm∸n≤suc[m∸n] : ∀ m n → suc m ∸ n ≤ suc (m ∸ n)
sucm∸n≤suc[m∸n] zero zero = s≤s 0≤n
sucm∸n≤suc[m∸n] zero (suc zero) = 0≤n
sucm∸n≤suc[m∸n] zero (suc (suc n)) = 0≤n
sucm∸n≤suc[m∸n] (suc m) zero = s≤s (s≤s refl-≤)
sucm∸n≤suc[m∸n] (suc m) (suc n) = sucm∸n≤suc[m∸n] m n

m∸n≤m : ∀ m n → m ∸ n ≤ m
m∸n≤m zero zero = 0≤n
m∸n≤m zero (suc n) = 0≤n
m∸n≤m (suc m) n
  with m∸n≤m m n
... | ind = begin≤
  suc m ∸ n ≤⟨ sucm∸n≤suc[m∸n] m n ⟩
  suc (m ∸ n) ≤⟨ s≤s (m∸n≤m m n) ⟩
  suc m ∎≤

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
longAnd _ zero = T
longAnd A (suc zero) = A
longAnd A (suc (suc n)) = A × longAnd A (suc n)
```
