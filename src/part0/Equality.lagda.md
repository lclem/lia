---
title: Equality🚧
---

```
{-# OPTIONS --rewriting --confluence-check #-}

module part0.Equality where
open import part0.Decidable public
open import Agda.Builtin.Equality public

private
  variable
    ℓ m n : Level
    A : Set ℓ
    B : Set m
    x y z : A

-- infix 4 _≡_ _≢_
-- data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set where
--     refl : x ≡ x

-- this helps with the rewrite directive
-- {-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

sym : x ≡ y → y ≡ x
sym refl = refl

inst1 : ∀ {B : Set m} → (A → B) → {{A}} → B
inst1 f {{a}} = f a

-- inst2 : ∀ {B : Set m} {C : Set n} → (A → B → C) → {{A}} → {{B}} → C
-- inst2 f {{a}} {{b}} = f a b

instance inst-sym : {{x ≡ y}} → y ≡ x
inst-sym {{x≡y}} = sym x≡y

trans : x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

instance inst-trans : {{x ≡ y}} → {{y ≡ z}} → x ≡ z
inst-trans {{arg1}} {{arg2}} = trans arg1 arg2

cong : (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

instance inst-cong : {{f : {A} → B}} {x y : A} → {{x ≡ y}} → f {x} ≡ f {y}
inst-cong {{f}} {{arg2}} = cong (λ x → f {x}) arg2

-- not very useful since higher-order unification is undecidable...
cong-auto : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {f : A → B} {x y : A} → x ≡ y → f x ≡ f y
cong-auto {f = f} = cong f

cong2 : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} (f : A → B → C) {x y : A} {z t : B} → x ≡ y → z ≡ t → f x z ≡ f y t
cong2 f refl refl = refl

-- curried version
cong2′ : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} (f : A → B → C) {x y : A} {z t : B} → (x ≡ y × z ≡ t) → f x z ≡ f y t
cong2′ f (refl , refl) = refl
```


```
Injective : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B) → Set (ℓ ⊔ m)
Injective f = ∀[ a0 ] ∀[ a1 ] (f a0 ≡ f a1 → a0 ≡ a1)

Injective2 : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} → (A → B → C) → Set (ℓ ⊔ m ⊔ n)
Injective2 f = ∀[ a0 ] ∀[ a1 ] ∀[ b0 ] ∀[ b1 ] (f a0 b0 ≡ f a1 b1 → a0 ≡ a1 × b0 ≡ b1)
```

```
cong2-inv : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} {f : A → B → C} {x y : A} {z t : B} → Injective2 f → f x z ≡ f y t → x ≡ y × z ≡ t
cong2-inv inj eq = inj _ _ _ _ eq

subst : ∀ {ℓ m} {A : Set ℓ} {x y : A} (P : A → Set m) → x ≡ y → P x → P y
subst P refl px = px

repl : ∀ {ℓ} {A B : Set ℓ} → A → A ≡ B → B
repl a refl = a

-- doesn't work since ends in "B"
-- "Terms marked as eligible for instance search should end with a name, so `instance' is ignored here."
--instance inst-repl : ∀ {A B : Set ℓ} → {{A}} → {{A ≡ B}} → B
--inst-repl {{a}} {{A≡B}} = repl a A≡B

infix  1 begin_
infixr 2 _≡⟨⟩_ _≡⟨_⟩_
infix  3 _∎

begin_ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → x ≡ y
begin x≡y = x≡y

_≡⟨⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y : A} → x ≡ y → x ≡ y
x ≡⟨⟩ x≡y = x≡y

_≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

_∎ : ∀ {ℓ} {A : Set ℓ} (x : A) → x ≡ x
x ∎ = refl

_≢_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Set ℓ
x ≢ y = ~ (x ≡ y)

~x≢x : ∀ {ℓ} {A : Set ℓ} {x : A} → ~ (x ≢ x)
~x≢x x≢x = x≢x refl

x≢x-elim : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x : A} → x ≢ x → B
x≢x-elim x≢x = F-elim (~x≢x x≢x)

sym-≢ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
sym-≢ x≢y refl = F-elim (x≢y refl)

≡-dfst : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {p q : Σ A B} →
  p ≡ q → dfst p ≡ dfst q
≡-dfst refl = refl

-- for dsnd p ≡ dsnd q we need eterogeneous equality

```

# Function extensionality

```
-- function extensionality
postulate extensionality : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {f g : Π A B} → ∀[ x ] f x ≡ g x → f ≡ g

```

# Decidable equality type class

```
record Eq {ℓ} (A : Set ℓ) : Set ℓ where
  infix 10 _≡?_
  field
    _≡?_ : ∀ (x y : A) → Dec (x ≡ y)

open Eq {{...}} public

refl-≡? : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (x : A) → x ≡? x ≡ yes _
refl-≡? x with x ≡? x
... | yes refl = refl
... | no x≢x = x≢x-elim x≢x

-- refl-≡?  is not a legal rewrite rule, since the left-hand side is neither a defined symbol nor a constructor when checking the pragma REWRITE refl-≡?
-- {-# REWRITE refl-≡? #-}
```

## Preservation of decidable equality

### Tagged unions

```
instance
  eq-⊎ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {{_ : Eq B}} → Eq (A ⊎ B)
  _≡?_ {{eq-⊎}} = go where

    go : ∀ x y → Dec (x ≡ y)
    go (left a) (left a')
      with a ≡? a'
    ... | yes refl = yes refl
    ... | no a≢a' = no λ{refl → a≢a' refl}
    go (left _) (right _) = no λ ()
    go (right x) (left x₁) = no λ ()
    go (right b) (right b')
      with b ≡? b'
    ... | yes refl = yes refl
    ... | no b≢b' = no λ{refl → b≢b' refl}
```

### Pairs

```
instance
  eq-× : ∀ {B : Set m} {{_ : Eq A}} {{_ : Eq B}} → Eq (A × B)
  _≡?_ {{eq-×}} (a1 , b1) (a2 , b2) with a1 ≡? a2
  ... | no a1≢a2 = no λ{refl → a1≢a2 refl}
  ... | yes refl with b1 ≡? b2
  ... | no b1≢b2 = no λ{refl → b1≢b2 refl}
  ... | yes refl = yes refl
```

### Dependent pairs

```
instance
  eqΣ : ∀ {B : A → Set m} {{_ : Eq A}} {{_ : ∀ {a} → Eq (B a)}} → Eq (Σ A B)
  _≡?_ {{eqΣ}} (a1 , b1) (a2 , b2) with a1 ≡? a2
  ... | no a1≢a2 = no λ{refl → a1≢a2 refl}
  ... | yes refl with b1 ≡? b2
  ... | no b1≢b2 = no λ{refl → b1≢b2 refl}
  ... | yes refl = yes refl
```

# Inspection idiom

```
data Inspect {A : Set ℓ} (x : A) : Set ℓ where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set ℓ} (x : A) → Inspect x
inspect x = it x refl
```
