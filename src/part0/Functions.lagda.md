---
title: Functions 🚧
---

```
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --rewriting --confluence-check #-}

module part0.Functions where
open import part0.Equality public

private
  variable
    ℓ m n : Level
    A : Set ℓ
    B : A → Set m
    C : Set m
    D : Set n

-- dependent flip!
flip : ∀ {D : A → C → Set n} → ((a : A) → (c : C) → D a c) → (c : C) → (a : A) → D a c
flip f c a = f a c

-- updating a function
infixl 300 _[_↦_]

update : {{_ : Eq A}} → Π A B → (a : A) → B a → Π A B
update f a b c
  with a ≡? c
... | yes refl = b
... | no _ = f c

_[_↦_] : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} → Π A B → (a : A) → B a → Π A B
(f [ a ↦ b ]) c = update f a b c

update-notReally : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} (x : A) (f : Π A B) → f [ x ↦ f x ] ≡ f
update-notReally {A} x f = extensionality go where

  go : ∀[ y ] (f [ x ↦ f x ]) y ≡ f y
  go y with x ≡? y
  ... | yes refl = refl
  ... | no _ = refl

updateSame : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} {ρ : Π A B} {x a} → ρ x ≡ a → ρ [ x ↦ a ] ≡ ρ
updateSame {ρ = ρ} {x = x} refl = update-notReally x ρ

-- vupdate-notReally : ∀ {n} (xs : Vector VarName n) (ρ : Valuation A) → ρ v[ xs ↦ vmap ρ xs ] ≡ ρ
-- vupdate-notReally = {!   !}

update-≡ : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} {ρ : Π A B}
  (x : A) {a : B x}
  → (ρ [ x ↦ a ]) x ≡ a
update-≡ x with x ≡? x
... | yes refl = refl
... | no x≢x = x≢x-elim x≢x

update-≡-rew : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} {ρ : Π A B}
  (x : A) {a : B x}
  → (update ρ x a) x ≡ a
update-≡-rew = update-≡

{- update-≡-rew  is not a legal rewrite rule, since the left-hand side 
update ρ x a x  reduces to  update ρ x a x | (x₁ Eq.≡? x) x
when checking the pragma REWRITE update-≡-rew -}

-- {-# REWRITE update-≡-rew #-}

update-≢ : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} {ρ : Π A B} {x y : A} {a : B x}
  → x ≢ y
  → (ρ [ x ↦ a ]) y ≡ ρ y
update-≢ {x = x} {y = y} x≢y with x ≡? y
... | yes refl = F-elim (x≢y refl)
... | no _ = refl

update-comm-pw : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}}
  (ρ : Π A B)
  (x y : A)
  (a : B x)
  (b : B y)
  → x ≢ y
  → ∀[ z ] (ρ [ x ↦ a ] [ y ↦ b ]) z ≡ (ρ [ y ↦ b ] [ x ↦ a ]) z
update-comm-pw ρ x y a b x≢y z with y ≡? z
... | yes refl
  with update-≢ {ρ = ρ [ y ↦ b ]} {a = a} x≢y
  -- ρ [ y ↦ b ] [ x ↦ a ] y ≡ ρ [ y ↦ b ] y
... | e1 = begin
  b               ≡⟨ sym (update-≡ y) ⟩
  (ρ [ y ↦ b ]) y ≡⟨ sym e1 ⟩
  (ρ [ y ↦ b ] [ x ↦ a ]) y ∎

update-comm-pw ρ x y a b x≢y z | no y≢z with x ≡? z
... | yes refl = refl
... | no x≢z = begin
  ρ z ≡⟨ sym (update-≢ {a = b} y≢z) ⟩
  (ρ [ y ↦ b ]) z
  ∎

update-comm : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}}
    (ρ : Π A B)
    (x y : A)
    (a : B x)
    (b : B y)
    → x ≢ y
    → ρ [ x ↦ a ] [ y ↦ b ] ≡ ρ [ y ↦ b ] [ x ↦ a ]
update-comm ρ x y a b neq = extensionality (update-comm-pw ρ x y a b neq)

update-comm-auto : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}}
    {ρ : Π A B}
    {x y : A}
    {a : B x}
    {b : B y}
    → x ≢ y
    → ρ [ x ↦ a ] [ y ↦ b ] ≡ ρ [ y ↦ b ] [ x ↦ a ]
update-comm-auto {ρ = ρ} {x} {y} {a} {b} = update-comm ρ x y a b

doubleupdate : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} {ρ : Π A B} (x : A) {a b : B x} →
  ρ [ x ↦ a ] [ x ↦ b ] ≡ ρ [ x ↦ b ]
doubleupdate {A = A} {ρ = ρ} x {a} {b} = extensionality p where
  p : (y : A) → (ρ [ x ↦ a ] [ x ↦ b ]) y ≡ (ρ [ x ↦ b ]) y
  p y with x ≡? y
  ... | yes refl = refl
  ... | no x≢y = update-≢ x≢y

updateUndo : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} {{_ : Eq A}} (ρ : Π A B) (a : A) {b : B a} →
  ρ [ a ↦ b ] [ a ↦ ρ a ] ≡ ρ
updateUndo ρ a = {!   !}

update-∘ : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {C : Set n} {{_ : Eq A}} (f : A → B) (g : B → C) (a : A) (b : B) → g ∘ (f [ a ↦ b ]) ≡ (g ∘ f) [ a ↦ g b ]
update-∘ f g a b = extensionality go where

  go : ∀ a′ → (g ∘ (f [ a ↦ b ])) a′ ≡ ((g ∘ f) [ a ↦ g b ]) a′
  go a′ with a ≡? a′
  ... | yes refl = refl
  ... | no _ = refl
```

## Function chains

```
infix  1 begin→_
infixr 2 _→⟨⟩_ _→⟨_⟩_ _by⟨_⟩_  -- _→≡⟨_⟩_
infix  3 _∎→ _QED

begin→_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B) → A → B
begin→ f = f

_→⟨⟩_ : ∀ {ℓ m} (A : Set ℓ) {B : Set m} → (A → B) → A → B
A →⟨⟩ A→B = A→B

_→⟨_⟩_ : ∀ {ℓ m n} (A : Set ℓ) {B : Set m} {C : Set n} → (A → B) → (B → C) → A → C
A →⟨ A→B ⟩ B→C = λ a → B→C (A→B a)

_by⟨_⟩_ = _→⟨_⟩_

--: ∀ {ℓ m n} (A : Set ℓ) {B : Set m} {C : Set n} → (A → B) → (B → C) → A → C
--A by⟨ A→B ⟩ B→C =

_∎→ : ∀ {ℓ} (A : Set ℓ) → A → A
A ∎→ = λ a → a

_QED = _∎→
```

Use case:

```
fcomp : ∀ (A B C : Set) → (A → B) → (B → C) → A → C
fcomp A B C f g =
    A by⟨ f ⟩
    B by⟨ g ⟩
    C QED 
```

# Currying

```
curry : ∀ {B : Set m} {C : Set n} → (A × B → C) → A → B → C
curry f a b = f (a , b)
```
