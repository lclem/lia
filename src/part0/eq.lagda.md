---
title: Equality
---

```
{-# OPTIONS --rewriting --confluence-check #-}

module part0.eq where
open import part0.logic
open import part0.decidable

infix 4 _≡_ _≢_
data _≡_ {ℓ} {A : Set ℓ} (x : A) : A → Set where
    refl : x ≡ x

-- this helps with the rewrite directive
{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REWRITE _≡_ #-}

sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- not very useful since higher-order unification is undecidable...
cong-auto : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {f : A → B} {x y : A} → x ≡ y → f x ≡ f y
cong-auto {f = f} = cong f

cong2 : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} (f : A → B → C) {x y : A} {z t : B} → x ≡ y → z ≡ t → f x z ≡ f y t
cong2 f refl refl = refl

subst : ∀ {ℓ m} {A : Set ℓ} {x y : A} (P : A → Set m) → x ≡ y → P x → P y
subst P refl px = px

repl : ∀ {ℓ} {A B : Set ℓ} → A → A ≡ B → B
repl a refl = a

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

_≢_ : ∀ {ℓ} {A : Set ℓ} (x y : A) → Set
x ≢ y = ¬ (x ≡ y)

¬x≢x : ∀ {ℓ} {A : Set ℓ} {x : A} → ¬ (x ≢ x)
¬x≢x x≢x = x≢x refl

x≢x-elim : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {x : A} → x ≢ x → B
x≢x-elim x≢x = ⊥-elim (¬x≢x x≢x)

sym-≢ : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≢ y → y ≢ x
sym-≢ x≢y refl = ⊥-elim (x≢y refl)

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

refl-≡? : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (x : A) → x ≡? x ≡ yes
refl-≡? x with x ≡? x
... | yes {refl} = refl
... | no {x≢x} = x≢x-elim x≢x

-- refl-≡?  is not a legal rewrite rule, since the left-hand side is neither a defined symbol nor a constructor when checking the pragma REWRITE refl-≡?
-- {-# REWRITE refl-≡? #-}
```

## Preservation of decidable equality

### Tagged unions

```
instance
  eq-⊎ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {{_ : Eq B}} → Eq (A ∨ B)
  _≡?_ {{eq-⊎}} = go where

    go : ∀ x y → Dec (x ≡ y)
    go (left a) (left a')
      with a ≡? a'
    ... | yes {refl} = yes {proof = refl}
    ... | no {a≢a'} = no {proof = λ{refl → a≢a' refl}}
    go (left _) (right _) = no {proof = λ ()}
    go (right x) (left x₁) = no {proof = λ ()}
    go (right b) (right b')
      with b ≡? b'
    ... | yes {refl} = yes {proof = refl}
    ... | no {b≢b'} = no {proof = λ{refl → b≢b' refl}}
```

### Dependent pairs

```
instance
  eqΣ : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} {{_ : ∀ {a} → Eq (B a)}} → Eq (Σ A B)
  _≡?_ {{eqΣ}} (a1 , b1) (a2 , b2) with a1 ≡? a2
  ... | no {a1≢a2} = no {proof = λ{ refl → a1≢a2 refl}}
  ... | yes {refl} with b1 ≡? b2
  ... | no {b1≢b2} = no {proof =  λ{ refl → b1≢b2 refl}}
  ... | yes {refl} = yes {proof = refl}
```



# Inspection idiom

```
data Inspect {ℓ} {A : Set ℓ} (x : A) : Set ℓ where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {ℓ} {A : Set ℓ} (x : A) → Inspect x
inspect x = it x refl
```
