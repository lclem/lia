---
title: Decidable properties🚧
---


```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.Decidable where
open import part0.Logic public

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  yes : A → Dec A
  no : ~ A → Dec A
```

# Preservation of decidability

## Function space

```
infixr 6 _→?_
_→?_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → Dec A → Dec B → Dec (A → B)
no ~a →? _ = yes λ a → F-elim (~a a)
yes a →? yes b = yes (const b)
yes a →? no ~b = no λ f → F-elim (~b (f a))

instance
  Dec-→ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{A? : Dec A}} {{B? : Dec B}} → Dec (A → B)
  Dec-→ {{A?}} {{B?}} = A? →? B?
```

```
infixr 7 _×?_
_×?_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → Dec A → Dec B → Dec (A × B)
yes x ×? yes y = yes (x , y)
no ~x ×? _ = no λ{ (x , y) → ~x x}
_ ×? no ~y = no λ{ (x , y) → ~y y}

instance
  Dec-× : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{A? : Dec A}} {{B? : Dec B}} → Dec (A × B)
  Dec-× {{A?}} {{B?}} = A? ×? B?

infixr 6 _⊎?_
_⊎?_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → Dec A → Dec B → Dec (A ⊎ B)
yes x ⊎? _ = yes (left x)
_ ⊎? yes y = yes (right y)
no ~x ⊎? no ~y = no λ{ (left x) → ~x x; (right y) → ~y y}

instance
  Dec-⊎ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{A? : Dec A}} {{B? : Dec B}} → Dec (A ⊎ B)
  Dec-⊎ {{A?}} {{B?}} = A? ⊎? B?

infix 8 ~?_
~?_ : ∀ {ℓ} {A : Set ℓ} → Dec A → Dec (~ A)
~? yes x = no (~~-intro x)
~? no ~x = yes (~x)

instance
  Dec-~ : ∀ {ℓ} {A : Set ℓ} {{A? : Dec A}} → Dec (~ A)
  Dec-~ {{A?}} = ~? A?

Decidable : ∀ {ℓ m} {A : Set ℓ} → (A → Set m) → Set (ℓ ⊔ m)
Decidable {A = A} P = ∀ (x : A) → Dec (P x)

Decidable2 : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} → (A → B → Set n) → Set (ℓ ⊔ m ⊔ n)
Decidable2 {A = A} {B = B} P = ∀ (a : A) (b : B) → Dec (P a b)
```

## Decidable properties behave classically

```  
-- you can use classical logic on decidable properties
contrapositive : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → Dec B → (~ B → ~ A) → A → B
contrapositive (yes (b)) p a = b 
contrapositive (no (~b)) p a =  F-elim (p ~b a)

doublenegation : ∀ {ℓ} {A : Set ℓ} → Dec A → ~ ~ A → A
doublenegation a? ~~a
  with a?
... | yes a = a 
... | no ~a = F-elim (~~a ~a) 
```

## Transport of decidability 

```
dec-iso : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → Dec A → (A ↔ B) → Dec B
dec-iso (yes a) (f , g) = yes (f a)
dec-iso (no ~a) (f , g) = no λ b → ~a (g b)
```