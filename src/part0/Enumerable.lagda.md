---
title: Enumerable types 🚧
---
  
```
{-# OPTIONS --allow-unsolved-meta #-}
-- {-# OPTIONS --rewriting  #-}

module part0.Enumerable where
open import part0.Booleans public
open import part0.Finite public
open import part0.List public

record Enum {ℓ} (A : Set ℓ) : Set ℓ where
  constructor _,_
  field
    enum : A *
    find : (a : A) → a ∈ enum

open Enum {{...}} public
```

## Booleans

```
instance
  Enum𝔹 : Enum 𝔹
  enum {{Enum𝔹}} = tt ∷ ff ∷ ε
  find {{Enum𝔹}} tt = here
  find {{Enum𝔹}} ff = there here
```

## Finite subsets of `ℕ`

```
enumFin : ∀ n → (Fin n) *
enumFin zero = ε
enumFin (suc n) = fzero ∷ map fsuc (enumFin n)

findFin : ∀ n → (i : Fin n) → i ∈ enumFin n
findFin _ fzero = here
findFin (suc n) (fsuc i) with findFin n i
... | i∈enumFin = there (map-∈ fsuc i∈enumFin)

instance
  EnumFin : ∀ {n} → Enum (Fin n)
  enum {{EnumFin {n}}} = enumFin n
  find {{EnumFin {n}}} = findFin n

enumFinLen : ∀ n → length (enumFin n) ≡ n
enumFinLen zero = refl
enumFinLen (suc n) with enumFinLen n
... | ind = cong suc goal where

  goal : length (map fsuc (enumFin n)) ≡ n
  goal = trans (map-length _ (enumFin n)) ind 
```

In general enumerations can contain repetitions.
Sometimes it is useful to have non-repeating enumerations.
This is the case for `enumFin` and we prove it below

In fact, we prove a stronger property first.

```
enumFin-Indices : ∀ n i j → i ∈ enumFin n ! j → Fin2ℕ i ≡ j
enumFin-Indices (suc _) fzero zero _ = refl

-- impossible case
enumFin-Indices (suc n) fzero (suc j) (there memb) = goal where

  have : ∃[ k ] k ∈ enumFin n ! j × fzero ≡ fsuc k
  have =  map-∈!-inv fzero fsuc (enumFin n) j memb

  impossible : fzero ≡ fsuc (dfst have)
  impossible = snd (dsnd have)

  goal : zero ≡ suc j
  goal with impossible
  ... | ()
  
enumFin-Indices (suc n) (fsuc i) (suc j) (there memb) = cong suc i≡j where

  i∈n!j : i ∈ enumFin n ! j
  i∈n!j = map-∈!-inv-easy i fsuc (enumFin n) j memb

  i≡j : Fin2ℕ i ≡ j
  i≡j = enumFin-Indices n i j  i∈n!j
```

We are now ready to prove that all elements in `enumFin` are distinct.

```
enumFinDistinct : ∀ n → distinct (enumFin n)
enumFinDistinct n i j k k∈n!i k∈n!j
  rewrite sym (enumFin-Indices _ _ _ k∈n!i) | sym (enumFin-Indices _ _ _ k∈n!j) = refl
```

## Enumerable functions

```
enumFun : ∀ {ℓ m} (A : Set ℓ) (B : Set m) {{_ : Eq A}} {{_ : Enum A}} {{_ : Enum B}} → (A → B) *
enumFun A B = go as bs where

  as : A *
  as = enum

  bs : B *
  bs = enum

  up : A → (A → B) → (A → B) *
  up a f = map (λ b → f [ a ↦ b ]) bs

  go : A * → B * → (A → B) *
  go ε ε = ε
  go ε (b ∷ _) = [ (const b) ]
  go (a ∷ as) bs = concatMap (up a) (go as bs)


findFun : ∀ {ℓ m} (A : Set ℓ) (B : Set m) {{_ : Eq A}} {{_ : Enum A}} {{_ : Enum B}} → (f : A → B) → f ∈ enumFun A B
findFun A B f = go as bs where

  as : A *
  as = enum

  bs : B *
  bs = enum

  go : A * → B * → f ∈ enumFun A B
  go = {!!}

instance
  EnumFun : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {{_ : Enum A}} {{_ : Enum B}} → Enum (A → B)
  enum {{EnumFun}} = enumFun _ _
  find {{EnumFun}} = findFun _ _
```

## Enumerable occurrences

Need that `a ∈? as` provably returns the first occurrence of `a` (if any).
Thus we use `a ∈1? as` here...

```
enum∈ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as : A *) → (a ∈ as) *
enum∈ a as with a ∈1? as
... | no = ε
enum∈ a (a ∷ as) | yes {here} = here ∷ map there (enum∈ a as)
enum∈ a (_ ∷ as) | yes {there _ _} = map there (enum∈ a as)

find∈ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as : A *) (a∈as : a ∈ as) → a∈as ∈ enum∈ a as
find∈ a as a∈as with a ∈1? as

-- contradiction
... | no {a∉1as} = F-elim (a∉1as (∈→∈1 a∈as)) 

find∈ a (a ∷ _) here | yes {here} = here
find∈ a (a ∷ as) (there a∈as) | yes {here} = there (map-∈ there (find∈ a as a∈as))

-- contradiction
-- here we use the fact that a ∈? as returns the first occurrence of a in as
find∈ a _ here | yes {there a≢a _} = x≢x-elim a≢a

find∈ a (_ ∷ as) (there a∈as) | yes {there _ _} = map-∈ there (find∈ a as a∈as)

instance
  Enum∈ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {a : A} {as : A *} → Enum (a ∈ as)
  enum {{Enum∈}} = enum∈ _ _
  find {{Enum∈}} = find∈ _ _
```

```
enum∈' : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) → (∃[ a ] a ∈ as) *
enum∈' = {!!}

find∈' : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) (p : ∃[ a ] a ∈ as) → p ∈ enum∈' as
find∈' = {!!}

instance
  Enum∈' : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as : A *} → Enum (∃[ a ] a ∈ as)
  enum {{Enum∈'}} = enum∈' _
  find {{Enum∈'}} = find∈' _
```

# Enumerations and decidability

We show that if we can enumerate elements,
then we can also decide decidable properties over them.

```
Π? : ∀ {ℓ m} (A : Set ℓ) {P : A → Set m} {{_ : Enum A}} → Decidable P → Dec (∀[ a ] P a)
Π? A {{enumA , findA}} P?
-- check whether every element in the enumeration satisfies A
  with All? P? enumA
-- in the positive case, use the find function to create a witness that "a" is in the enumeration,
-- and then use the fact that every element in the enumeration satisfies the property
... | yes {∀P} = yes {proof = λ a → ∀P (findA a)}
-- in the negative case, go the other way around (even easier, no need for "findA")
... | no {~∀P} = no {proof = λ ∀aP → ~∀P (λ {a} a∈enumA → ∀aP a)}

forAll? : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} {{_ : Enum A}} → Decidable P → Dec (∀[ a ] P a)
forAll? {A = A} P? = Π? A P?

-- alternative: look at ~ P and apply enumDec∀
Σ? : ∀ {ℓ m} (A : Set ℓ) {P : A → Set m} {{_ : Enum A}} → Decidable P → Dec (∃[ a ] P a)
Σ? A {{enumA , findA}} P?
  with Any? P? enumA
... | yes {∃P} = yes {proof = dfst ∃P , snd (dsnd ∃P)} -- can't pattern match on ∃P here since the first projection is implicit
... | no {~∃P} = no {proof = λ{ (a , Pa) → ~∃P (a , findA a , Pa)}}

thereExists? : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} {{_ : Enum A}} → Decidable P → Dec (∃[ a ] P a)
thereExists? {A = A} P? = Σ? A P?

infix 0 forAll? thereExists?
syntax forAll? (λ a → P) = ∀?[ a ] P
syntax thereExists? (λ a → P) = ∃?[ a ] P
```

```
-- this one additionally requires enumerability of the domain A;
-- the other implication holds without any assumption on A, B;
-- the implication "~ ∃[ a ] ~ B a → ∀[ a ] B a" requires decidability of B, but not enumerability of A
-- TODO: refactor using the analogous property for lists ~∀∈→∃∈~
deMorgan-~∀~→∃ : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} → Enum A → Decidable B → ~ (∀[ a ] ~ B a) → ∃[ a ] B a
deMorgan-~∀~→∃ {A = A} {B} (enumA , findA) B? ~∀~B = go enumA ε refl where

  go : (as : A *) → (~Bs : (∃[ a ] ~ B a) *) → enumA ≡ map dfst ~Bs ++ as → ∃[ a ] B a
  go ε ~Bs refl = F-elim (~∀~B ∀a~Ba) where

    ∀a~Ba : ∀[ a ] ~ B a
    ∀a~Ba a Ba = ~Ba Ba where

      a∈~Bs : a ∈ map dfst ~Bs
      -- could use REWRITE here to silently reduce a ∈ map dfst ~Bs ++ ε to ε
      a∈~Bs rewrite ++ε (map dfst ~Bs) = findA a

      ~Ba : ~ B a
      ~Ba with map-∈-inv dfst a∈~Bs
      ... | (a , ~Ba) , _ , a≡dfst rewrite a≡dfst = ~Ba
      
  go (a ∷ as) ~Bs enumA≡
    with B? a
  ... | yes {Ba} = a , Ba
  ... | no {~Ba} = go as (~Bs ++ [ (a , ~Ba) ]) enumA≡' where

    enumA≡' : enumA ≡ map dfst (~Bs ++ [ (a , ~Ba) ]) ++ as
    enumA≡' = begin
      enumA ≡⟨ enumA≡ ⟩
      map dfst ~Bs ++ (a ∷ as) ≡⟨ ++-middle (map dfst ~Bs) a as ⟩
      (map dfst ~Bs ++ [ a ]) ++ as ≡⟨⟩
      (map dfst ~Bs ++ [ (dfst (a , ~Ba)) ]) ++ as ≡⟨⟩
      (map dfst ~Bs ++ map dfst ([ (a , ~Ba) ])) ++ as ≡⟨ cong (λ bs → bs ++ as) (map-++ dfst ~Bs ([(a , ~Ba)])) ⟩
      map dfst (~Bs ++ [ (a , ~Ba) ]) ++ as ∎
```

# Enumerations and equality

We show that functions `A → B` from an enumerable domain `A` to a domain `B` with decidable equality
have decidable equality (assuming extensionality).

```
--instance
--  eqA→B : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq B}} {{_ : Enum A}} → Eq (A → B)
--  _≡?_ {{eqA→B}} f g = {!!}
```
