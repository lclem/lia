---
title: Decidable properties🚧
---


```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.Decidable where
open import part0.Logic public

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  instance yes : {proof : A} → Dec A
  instance no : {proof : ~ A} → Dec A
```

# Preservation of decidability

## Function space

```
infixr 6 _→?_
_→?_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → Dec A → Dec B → Dec (A → B)
no {~a} →? _ = yes {proof = λ a → F-elim (~a a)}
yes {a} →? yes {b} = yes {proof = const b}
yes {a} →? no {~b} = no {proof = λ f → F-elim (~b (f a))}

instance
  Dec-→ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{A? : Dec A}} {{B? : Dec B}} → Dec (A → B)
  Dec-→ {{A?}} {{B?}} = A? →? B?
```

```
infixr 7 _×?_
_×?_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → Dec A → Dec B → Dec (A × B)
yes {x} ×? yes {y} = yes {proof = x , y}
no {~x} ×? _ = no {proof = λ{ (x , y) → ~x x}}
_ ×? no {~y} = no {proof = λ{ (x , y) → ~y y}}

instance
  Dec-× : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{A? : Dec A}} {{B? : Dec B}} → Dec (A × B)
  Dec-× {{A?}} {{B?}} = A? ×? B?

infixr 6 _⊎?_
_⊎?_ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → Dec A → Dec B → Dec (A ⊎ B)
yes {x} ⊎? _ = yes {proof = left x}
_ ⊎? yes {y} = yes {proof = right y}
no {~x} ⊎? no {~y} = no {proof = λ{ (left x) → ~x x; (right y) → ~y y}}

instance
  Dec-⊎ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{A? : Dec A}} {{B? : Dec B}} → Dec (A ⊎ B)
  Dec-⊎ {{A?}} {{B?}} = A? ⊎? B?

infix 8 ~?_
~?_ : ∀ {ℓ} {A : Set ℓ} → Dec A → Dec (~ A)
~? yes {x} = no {proof = ~~-intro x}
~? no {~x} = yes {proof = ~x}

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
contrapositive (yes {proof = b}) p a = b 
contrapositive (no {proof = ~b}) p a =  F-elim (p ~b a)

doublenegation : ∀ {ℓ} {A : Set ℓ} → Dec A → ~ ~ A → A
doublenegation a? ~~a
  with a?
... | yes {a} = a 
... | no {~a} = F-elim (~~a ~a) 
```
