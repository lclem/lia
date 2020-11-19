---
title: Lists🚧
---

```
-- {-# OPTIONS --termination-depth=10 #-}
{-# OPTIONS --allow-unsolved-metas --overlapping-instance #-}
{-# OPTIONS --rewriting  #-}

-- --confluence-check gives:
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Rewriting/Confluence.hs:555

module part0.List where
open import part0.Naturals public
open import part0.Functions public

infixr 25 _∷_
data _* {ℓ} (A : Set ℓ) : Set ℓ where
    ε : A *
    _∷_ : A → A * → A *

tail : ∀ {ℓ} {A : Set ℓ} → A * → A *
tail ε = ε
tail (_ ∷ as) = as

--TODO: use the variable mechanism to reduce clutter

--variable

--  ℓ : Level
--  A : Set ℓ
  
--  a a' : A
--  as as' : A *
```

# Injectivity of the constructors

```

∷-inj-left : ∀ {ℓ} {A : Set ℓ} {a a' : A} {as as' : A *} → a ∷ as ≡ a' ∷ as' → a ≡ a'
∷-inj-left refl = refl

∷-inj-right : ∀ {ℓ} {A : Set ℓ} {a a' : A} {as as' : A *} → a ∷ as ≡ a' ∷ as' → as ≡ as'
∷-inj-right refl = refl
```

```
cons-≡1 : ∀ {ℓ} {A : Set ℓ} {a b : A} {as bs : A *} → a ∷ as ≡ b ∷ bs → a ≡ b × as ≡ bs
cons-≡1 refl = refl , refl

cons-≡2 : ∀ {ℓ} {A : Set ℓ} {a b : A} {as bs : A *} → a ≡ b → as ≡ bs → a ∷ as ≡ b ∷ bs
cons-≡2 refl refl = refl

-- equality is decidable on A *, if it is on A}
instance
  eqList : ∀ {ℓ} {A : Set ℓ} → {{Eq A}} → Eq (A *)
  _≡?_ {{eqList}} ε ε = yes refl
  _≡?_ {{eqList}} ε (_ ∷ _) = no (λ ())
  _≡?_ {{eqList}} (_ ∷ _) ε  = no (λ ())
  _≡?_ {{eqList}} (a ∷ as) (b ∷ bs) with a ≡? b
  ... | no proof = no (λ p → proof (fst (cons-≡1 p)))
  ... | yes refl with as ≡? bs
  ... | yes refl = yes refl
  ... | no proof = no (λ p → proof (snd (cons-≡1 p)))

Fun : ∀ {ℓ} (A : Set ℓ) (B : Set ℓ) (n : ℕ) → Set ℓ
Fun A B zero = B
Fun A B (suc n) = A → Fun A B n


[ : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → Fun A (A *) n
[ {A = A} {n = n} = go n ε where

  -- this reverses the list!
  go : ∀ n → A * → Fun A (A *) n
  go zero as = as
  go (suc n) as a = go n (a ∷ as) 

-- we need to reverse the list at the end
infix 100 _]
_] : ∀ {ℓ} {A : Set ℓ} → A * → A *
_] {A = A} as = go as ε where

  go : A * → A * → A *
  go ε bs = bs
  go (a ∷ as) bs = go as (a ∷ bs)

singleton : ∀ {ℓ} {A : Set ℓ} → A → A *
singleton a = [ a ]

_ : ℕ *
_ = [ 1  2  3 ]
```

## Length

```
length : ∀ {ℓ} {A : Set ℓ} → A * → ℕ
length ε = zero
length (_ ∷ as) = suc (length as)
```

## Map

```
map : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B) → A * → B *
map _ ε = ε
map f (a ∷ as) = f a ∷ map f as

map-∘ : ∀ {ℓ m o} {A : Set ℓ} {B : Set m} {C : Set o} (f : A → B) (g : B → C) (as : A *) →
  map g (map f as) ≡ map (g ∘ f) as
map-∘ _ _  ε = refl
map-∘ f g (a ∷ as) with map-∘ f g as
... | eq = cong (λ as → g (f a) ∷ as) eq

map-length : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B) (xs : A *) → length (map f xs) ≡ length xs
map-length _ ε = refl
map-length f (_ ∷ xs) = cong suc (map-length f xs)
```

## Reversal

```
reverse : ∀ {ℓ} {A : Set ℓ} → A * → A *
reverse {A = A} as = go as ε where

  go : A * → A * → A *
  go ε bs = bs
  go (a ∷ as) bs = go as (a ∷ bs)
```

## Append

```
infixr 25 _++_
_++_ : ∀ {ℓ} {A : Set ℓ} → A * → A * → A *
ε ++ bs = bs
(a ∷ as) ++ bs = a ∷ (as ++ bs)

++ε : ∀ {ℓ} {A : Set ℓ} (as : A *) → as ++ ε ≡ as
++ε ε = refl
++ε (a ∷ as) with ++ε as
... | as++ε≡as = cong (λ bs → a ∷ bs) as++ε≡as

{-# REWRITE ++ε #-}

assoc-++ : ∀ {ℓ} {A : Set ℓ} (as bs cs : A *) → (as ++ bs) ++ cs ≡ as ++ bs ++ cs
assoc-++ = {!!}

{-# REWRITE assoc-++ #-}

++-middle : ∀ {ℓ} {A : Set ℓ} (as : A *) (a : A) (bs : A *) → as ++ a ∷ bs ≡ (as ++ [ a ]) ++ bs
++-middle = {!!}

-- this should be the other way around:
-- map f (as ++ bs) ≡ map f as ++ map f bs
map-++ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B) (as bs : A *) → map f as ++ map f bs ≡ map f (as ++ bs)
map-++ f ε bs = refl
map-++ f (a ∷ as) bs rewrite map-++ f as bs = refl
```

## Fold

```
foldl : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (B → A → B) → B → A * → B
foldl f b ε = b
foldl f b (a ∷ as) = foldl f (f b a) as

foldr : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B → B) → B → A * → B
foldr f b ε = b
foldr f b (a ∷ as) = f a (foldr f b as)

foldr1 : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → A → A) → A → A * → A
foldr1 _ a ε = a
foldr1 _ _ (a ∷ ε) = a
foldr1 {A = A} {B = B} f a (a' ∷ as) = f a' (foldr1 {A = A} {B = B} f a as)
```

## Concatenation

```
concat : ∀ {ℓ} {A : Set ℓ} → A * * → A *
concat = foldl _++_ ε

-- example
_ : concat ([ ([ 1 2 ]) ([ 3 4 ]) ]) ≡ [ 1 2 3 4 ]
_ = refl

concatMap : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → (A → B *) → A * → B *
concatMap f = concat ∘ map f
```

## Filter

```
filter : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} → Decidable P → A * → A *
filter _ ε = ε
filter P? (a ∷ as) with P? a
... | yes _ = a ∷ filter P? as
... | no _ = filter P? as
```

## Remove

```
remove : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} → A → A * → A *
remove a = filter λ x → ~? (x ≡? a)

remove-map : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {{_ : Eq B}}
  {f : A → B} →
  Injective f →
  (b : A) →
  (as : A *) →
  map f (remove b as) ≡ remove (f b) (map f as)
remove-map _ _ ε = refl
remove-map {f = f} inj b (a ∷ as)
  with remove-map inj b as
... | ind
  with a ≡? b | f a ≡? f b
-- both equal, by induction
... | yes _ | yes _ rewrite ind = refl
-- both unequal, by induction
... | no _ | no _ rewrite ind = refl
-- contradiction, just by functionality
... | yes refl | no fa≢fa = x≢x-elim fa≢fa
-- contradiction, by injectivity
... | no a≢b | yes fa≡fb = F-elim (a≢b a≡b) where

  a≡b : a ≡ b
  a≡b = inj a b fa≡fb
```

## Get

```
get : ∀ {ℓ} {A : Set ℓ} → ℕ → A * → A → A
get _ ε a = a
get zero (a ∷ _) _ = a
get (suc n) (_ ∷ as) a = get n as a

get-ne : ∀ {ℓ} {A : Set ℓ} (n : ℕ) (as : A *) → length as > n → A
get-ne zero (a ∷ _) _ = a
get-ne (suc n) (_ ∷ as) len>sucn = get-ne n as (suc-< len>sucn)

last : ∀ {ℓ} {A : Set ℓ} (as : A *) → length as > 0 → A
last (a ∷ ε) _ = a
last (_ ∷ a ∷ as) _ =  last (a ∷ as) (s≤s 0≤n)
```

## Drop

```
module drop where

  drop : ∀ {ℓ} {A : Set ℓ} → ℕ → A * → A *
  drop _ ε = ε
  drop zero as = as
  --drop (suc _) ε = ε
  drop (suc m) (_ ∷ as) = drop m as

  -- drop-ε : ∀ n -> drop n ε ≡ ε
  -- drop-ε zero = refl
  -- drop-ε (suc n) = refl

  drop-zero : ∀ {ℓ} {A : Set ℓ} (as : A *) → drop zero as ≡ as
  drop-zero ε = refl
  drop-zero (_ ∷ _) = refl

  drop-map : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B) (n : ℕ) (as : A *) → drop n (map f as) ≡ map f (drop n as)
  drop-map f zero as = {!!} -- refl
  drop-map f (suc n) (_ ∷ as) = drop-map f n as
  drop-map f (suc n) ε = refl

  drop-map-cons : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B) (n : ℕ) (as : A *) (a : A) → drop n (f a ∷ map f as) ≡ map f (drop n (a ∷ as))
  drop-map-cons _ zero _ _ = refl
  drop-map-cons f (suc n) as a = drop-map f n as

  drop-all : ∀ {ℓ} {A : Set ℓ} (as : A *) → drop (length as) as ≡ ε
  drop-all ε = refl
  drop-all (_ ∷ as) = drop-all as

  drop-cons : ∀ {ℓ} {A : Set ℓ} (m : ℕ) (as : A *) (len>m : length as > m) →
    drop m as ≡ get-ne m as len>m ∷ drop (suc m) as
  drop-cons zero (a ∷ as) len>m = {!!} -- refl
  drop-cons (suc m) (_ ∷ as) (s≤s len>m) = drop-cons m as len>m
  
open drop public
```

```
infix 5 _∈_ _∈?_ _∉_ _~∈_
data _∈_ {ℓ} {A : Set ℓ} : A → A * → Set where
    here : ∀ {x} {xs : A *} → x ∈ (x ∷ xs)
    there : ∀ {x y} {xs : A *} (x∈xs : x ∈ xs) → x ∈ (y ∷ xs)

∈→∈++-left : ∀ {ℓ} {A : Set ℓ} {a : A} {as : A *} (bs : A *) → a ∈ as → a ∈ as ++ bs
∈→∈++-left _ here = here
∈→∈++-left {a = a} {_ ∷ as} bs (there a∈as) = there (∈→∈++-left {a = a} {as} bs a∈as)

∈→∈++-right : ∀ {ℓ} {A : Set ℓ} {a : A} (as : A *) {bs : A *} → a ∈ bs → a ∈ as ++ bs
∈→∈++-right = {!!}

-- TODO: make "as" explicit and live with it
a∈as++bs→a∈as⊎a∈bs : ∀ {ℓ} {A : Set ℓ} {a : A} {as bs : A *} → a ∈ as ++ bs → a ∈ as ⊎ a ∈ bs
a∈as++bs→a∈as⊎a∈bs {a = a} {ε} {bs} a∈as++bs = right a∈as++bs
a∈as++bs→a∈as⊎a∈bs {a = _} {_ ∷ as} {bs} here = left here
a∈as++bs→a∈as⊎a∈bs {a = a} {_ ∷ as} {bs} (there a∈as++bs) with a∈as++bs→a∈as⊎a∈bs {as = as} a∈as++bs
... | left a∈as = left (there a∈as)
... | right a∈bs = right a∈bs

∈++-choose : ∀ {ℓ} {A : Set ℓ} {a : A} (as : A *) {bs : A *} → a ∈ as ++ bs → a ∈ as ⊎ a ∈ bs
∈++-choose _ = a∈as++bs→a∈as⊎a∈bs

_~∈_ : ∀ {ℓ} {A : Set ℓ} → A → A * → Set
a ~∈ as = ~ (a ∈ as)

~∈-∷-left : ∀ {ℓ} {A : Set ℓ} {a b : A} {as : A *} →
  a ~∈ b ∷ as →
  a ≢ b
~∈-∷-left a~∈b∷as refl = a~∈b∷as here

~∈-∷-right : ∀ {ℓ} {A : Set ℓ} {a b : A} {as : A *} →
  a ~∈ b ∷ as →
  a ~∈ as
~∈-∷-right a~∈b∷as a∈as = a~∈b∷as (there a∈as)

_∈?_ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as : A *) → Dec (a ∈ as)
a ∈? ε = no (λ ())
a ∈? b ∷ as with a ≡? b
... | yes refl = yes (here)
... | no a≢b with a ∈? as
... | yes a∈as = yes (there a∈as)
... | no ~a∈as = no (goal) where
  goal : ~ (a ∈ b ∷ as)
  goal here = a≢b refl
  goal (there a∈as) = ~a∈as a∈as

All : ∀ {ℓ m} {A : Set ℓ} → (A → Set m) → A * → Set (ℓ ⊔ m)
All {A = A} P as = ∀ {a : A} → a ∈ as → P a

Any : ∀ {ℓ m} {A : Set ℓ} → (A → Set m) → A * → Set (ℓ ⊔ m)
Any {A = A} P as = ∃[ a ] a ∈ as × P a -- "a" is NOT implicit

infix 0 All Any
syntax All (λ a → P) as = ∀[ a ∈ as ] P
syntax Any (λ a → P) as = ∃[ a ∈ as ] P

-- example

_ : (A : Set) (as : A *) → ∀[ a ∈ as ] T
_ = λ A as a∈as → tt

_ : (A : Set) (as : A *) (b : A) → ∃[ a ∈ (b ∷ as) ] T
_ = λ A as b → _ , here , tt

-- interesting non-trivial exercise;
-- can push negation through quantified membership
~∀∈→∃∈~ : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} →
  Decidable P →
  (as : A *) →
  ~ (∀[ a ∈ as ] P a)
  → ∃[ a ∈ as ] ~ P a
~∀∈→∃∈~ {A = A} {P} P? as ~∀[a∈as]Pa = go as ε {!!} refl where

  -- bs is the elements to be processed
  -- cs is the elements already processed,
  -- for which we know that P holds
  -- the invariant tells us that as ≡ cs ++ bs
  go : (bs : A *) → (cs : A *) → (∀[ a ∈ cs ] P a) → as ≡ cs ++ bs → ∃[ a ∈ as ] ~ P a
  -- in the base case, we searched the whole list "as" for an element a s.t. ~ P a, with no success
  -- thus the invariant Ps tells use that all elements satisfy P a
  go ε cs inv refl = F-elim (~∀[a∈as]Pa inv)      
  go (b ∷ bs) cs inv refl
    with P? b
  -- if the current element b does not satisfy P, then we are done
  ... | no ~Pb = b , ∈→∈++-right _ here , ~Pb
  -- otherwise, b satisfies ~ ~ P (i.e., P since it is decidable)
  ... | yes Pb = go bs (cs ++ [ b ]) inv' refl where

    inv' : ∀[ a ∈ cs ++ [ b ] ] P a
    inv' {a} a∈cs++b
      with a∈as++bs→a∈as⊎a∈bs {as = cs} {bs = [ b ]} a∈cs++b
    ... | left a∈cs = inv a∈cs
    ... | right here = Pb

-- decide whether every element in a list satisfies a decidable property
All? : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} → Decidable P → (as : A *) → Dec (∀[ a ∈ as ] P a)
All? P? ε = yes (λ ())
All? P? (a ∷ as)
  with P? a
... | no ~P?a = no (λ z → ~P?a (z here))
... | yes P?a
  with All? P? as
... | no ~All?as = no λ z → ~All?as λ z₁ → z (there z₁)
... | yes All?as = yes λ{here → P?a ; (there a∈as) → All?as a∈as}

-- use All?, ~∀∈→∃∈~, and the fact that the double negation law holds for decidable properties
Any? : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} → Decidable P → (as : A *) → Dec (∃[ a ∈ as ] P a)
Any? P? as
  with All? (~?_ ∘ P?) as
... | yes ~p = no λ{ (a , a∈as , Pa) → ~p a∈as Pa}
... | no ~~p
  with ~∀∈→∃∈~ (~?_ ∘ P?) as ~~p
... | a , a∈as , ~~Pa = yes (a , a∈as , doublenegation (P? a) ~~Pa)

infix 0 All? Any?
syntax All? (λ a → P) as = ∀?[ a ∈ as ] P
syntax Any? (λ a → P) as = ∃?[ a ∈ as ] P

head : ∀ {ℓ} {A : Set ℓ} (as : A *) → as ≡ ε ⊎ (∃[ a ] a ∈ as)
head ε = left refl
head (a ∷ _) = right (a , here)

instance
  eq∈ : ∀ {ℓ} {A : Set ℓ} {a : A} {as : A *} → Eq (a ∈ as)
  _≡?_ {{eq∈}} here here = yes refl
  _≡?_ {{eq∈}} here (there _) = no (λ ())
  _≡?_ {{eq∈}} (there _) here = no (λ ())
  _≡?_ {{eq∈}} (there a∈as1) (there a∈as2) with a∈as1 ≡? a∈as2
  ... | yes refl = yes refl
  ... | no a∈as1≢a∈as2 = no λ{refl → x≢x-elim a∈as1≢a∈as2}
```

### Filter

```
filter-∈ : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} {P? : Decidable P} {a : A} {as : A *} →
  a ∈ as →
  P a →
  a ∈ filter P? as
filter-∈ = {!   !}

filter-∈2 : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} {P? : Decidable P} {a : A} {as : A *} →
  a ∈ as →
  a ∈ filter P? as ⊎ ~ P a
filter-∈2 {P? = P?} {a} a∈as
  with P? a
... | yes Pa = left (filter-∈ a∈as Pa)
... | no ~Pa = right ~Pa

filter-∈-inv : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} {P? : Decidable P} {a : A} (as : A *) →
  a ∈ filter P? as →
  a ∈ as × P a
filter-∈-inv = {!   !}
```

### Map

```
map-∈ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {a : A} (f : A → B) {as : A *} →
  a ∈ as →
  f a ∈ map f as
map-∈ f here = here
map-∈ f (there a∈as) = there (map-∈ f a∈as)

map-∈-conv : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (a : A) (f : A → B) {as : A *} →
  f a ~∈ map f as →
  a ~∈ as
map-∈-conv a f fa∉mapfas a∈as = fa∉mapfas (map-∈ f a∈as)

map-∈-inv : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {b : B} (f : A → B) {as : A *} →
  b ∈ map f as →
  ∃[ a ∈ as ] b ≡ f a
map-∈-inv f b∈mapfas = {!x!}
```

### Remove

```
-- one could give an alternative proof via filter-∈2
remove-∈ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {a : A} {as : A *} (b : A) →
  a ∈ as →
  a ∈ remove b as ⊎ a ≡ b
remove-∈ {a = a} b here
  with a ≡? b
... | yes a≡b = right a≡b
... | no a≢b = left here
remove-∈ {a = a} {c ∷ as} b (there a∈as)
  with remove-∈ b a∈as
... | right a≡b = right a≡b
... | left a∈rem
  with c ≡? b
... | yes c≡b = left a∈rem
... | no c≢b = left (there a∈rem)

remove-∈-inv : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {b : A} {a : A} {as : A *} → b ∈ remove a as → b ∈ as × b ≢ a
remove-∈-inv = {!!}
```

```
~∈-++-left : ∀ {ℓ} {A : Set ℓ} {a : A} {as bs : A *} →
  a ~∈ as ++ bs →
  a ~∈ as
~∈-++-left = {!!}

-- for some reason it won't guess the as right
~∈-++-right : ∀ {ℓ} {A : Set ℓ} {a : A} (as : A *) {bs : A *} →
  a ~∈ as ++ bs →
  a ~∈ bs
~∈-++-right = {!!}

data _∉_ {ℓ} {A : Set ℓ} : A → A * → Set ℓ where
  notHere : ∀ {x} → x ∉ ε
  notThere : ∀ {x y} {xs} → x ≢ y → x ∉ xs → x ∉ (y ∷ xs)

-- the easy direction
∉Lemma1 ∉→~∈ : ∀ {ℓ} {A : Set ℓ} {a : A} {as : A *} → a ∉ as → a ~∈ as
∉Lemma1 = ∉→~∈

∉→~∈ notHere ()
∉→~∈ {a = a} {a ∷ as} (notThere a≢b a∉as) here = ~x≢x a≢b
∉→~∈ {a = a} {b ∷ as} (notThere a≢b a∉as) (there a∈as) = ∉→~∈ a∉as a∈as

-- the more difficult direction
∉Lemma2 ~∈→∉ : ∀ {ℓ} {A : Set ℓ} {a : A} {as : A *} → a ~∈ as → a ∉ as
∉Lemma2 = ~∈→∉

~∈→∉ {as = ε} _ = notHere
~∈→∉ {as = b ∷ as} a~∈b∷as
  with ~∈-∷-left a~∈b∷as |
       ~∈-∷-right a~∈b∷as
... | a≢b | a~∈as
  -- recursive call
  with ~∈→∉ a~∈as
... | a∉as = notThere a≢b a∉as

∉-++-left : ∀ {ℓ} {A : Set ℓ} {a : A} {as bs : A *} →
  a ∉ as ++ bs →
  a ∉ as
∉-++-left = {!!}

∉-++-right : ∀ {ℓ} {A : Set ℓ} {a : A} {as bs : A *} →
  a ∉ as ++ bs →
  a ∉ bs
∉-++-right = {!!}

∉-concat : ∀ {ℓ} {A : Set ℓ} {a : A} {as : A *} {ass : A * *} →
  a ∉ concat ass →
  as ∈ ass →
  a ∉ as
∉-concat p q = {!   !}

~∈ε : ∀ {ℓ} {A : Set ℓ} {a : A} → ~ (a ∈ ε)
~∈ε ()

remove-~∈ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as : A *) → a ~∈ remove a as
remove-~∈ a as = {!   !}

infix 6 _∈_!_
data _∈_!_ {ℓ} {A : Set ℓ} : A → A * → ℕ → Set where
  here : ∀ {x} {xs : A *} → x ∈ (x ∷ xs) ! zero
  there : ∀ {x y} {n} {xs : A *} → x ∈ xs ! n → x ∈ (y ∷ xs) ! (suc n)

there-inj : ∀ {ℓ} {A : Set ℓ} {a b : A} {n} {as : A *} → a ∈ (b ∷ as) ! (suc n) → a ∈ as ! n
there-inj (there memb) = memb

-- an equality principle for lists
listEqPrinciple : ∀ {ℓ} {A : Set ℓ} (as bs : A *) → length as ≡ length bs → (∀ a k → a ∈ as ! k → a ∈ bs ! k) → as ≡ bs
listEqPrinciple ε ε len memb = refl
listEqPrinciple (a ∷ as) (b ∷ bs) len memb
  with
    let memb' a k a∈as!k = there-inj (memb a (suc k) (there a∈as!k)) in
    listEqPrinciple as bs (suc-inj len) memb'
... | refl with memb a zero here
... | here = refl

∈→∈! :  ∀ {ℓ} {A : Set ℓ} (a : A) (as : A *) → a ∈ as → ∃[ k ] a ∈ as ! k
∈→∈! a (a ∷ _) here = zero , here
∈→∈! a (_ ∷ as) (there a∈as) with ∈→∈! a as a∈as
... | (k , a∈as!k) = suc k , there a∈as!k

∈!→∈ : ∀ {ℓ} {A : Set ℓ} (a : A) (as : A *) (k : ℕ) → a ∈ as ! k → a ∈ as
∈!→∈ = {!!}

map-∈! : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (a : A) (f : A → B) (as : A *) (k : ℕ) →
  a ∈ as ! k →
  f a ∈ map f as ! k
map-∈! a f _ k here = here
map-∈! a f (_ ∷ as) (suc k) (there a∈as) = there (map-∈! a f as k a∈as)

map-∈!-inv-easy : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (a : A) (f : A → B) (as : A *) (k : ℕ) →
  f a ∈ map f as ! k →
  a ∈ as ! k
map-∈!-inv-easy a f as k = {!x!}

map-∈!-inv : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (b : B) (f : A → B) (as : A *) (k : ℕ) →
  b ∈ map f as ! k →
  ∃[ a ] a ∈ as ! k × b ≡ f a
map-∈!-inv f x = {!x!}

get-ne-∈! : ∀ {ℓ} {A : Set ℓ} → (k : ℕ) (as : A *) (len>k : length as > k) → get-ne k as len>k ∈ as ! k
get-ne-∈! zero (a ∷ as) cond = here
get-ne-∈! (suc k) (a ∷ as) (s≤s cond) with get-ne-∈! k as cond
... | ind = there ind

drop-∈! : ∀ {ℓ} {A : Set ℓ} a m (as : A *) k → a ∈ drop m as ! k → a ∈ as ! (m + k)
drop-∈! a zero as k memb rewrite drop-zero as = memb
drop-∈! a (suc m) (_ ∷ as) k memb with drop-∈! a m as k memb
... | ind = there ind


data TList {ℓ} : (Set ℓ) * → Set ℓ where
    ε : TList ε
    _∷_ : ∀ {A : Set ℓ} {As : (Set ℓ) *} → A → TList As → TList (A ∷ As)

-- tmap : ∀ {ℓ} {As Bs : Vector (Set ℓ) n} → TVector {ℓ} {n} (zipWith Fun As Bs) → TList As → TList Bs
-- tmap {ε} {ε} ε ε = ε
-- tmap {A ∷ As} {B ∷ Bs} (f ∷ fs) (a ∷ as) = f a ∷ tmap fs as

-- tfilter :

-- dependent map over a list
dmap : ∀ {ℓ m} {A : Set ℓ} {B : A → Set m} → Π A B → (as : A *) → TList (map B as)
dmap _ ε = ε
dmap f (a ∷ as) = f a ∷ dmap f as

-- filter-proof : ∀ {A : Set} {P : A → Set} → (P? : Decidable P) → (as : A *) → TList {! map (Dec ∘ P) as  !}
-- filter-proof {A} {P} P? as = {!   !} where
--
--   as? : TList (map (Dec ∘ P) as)
--   as? = dmap P? as

maximum : ℕ * → ℕ → ℕ
maximum ε default = default
maximum (n ∷ ns) default with maximum ns default
... | max with n ≤? max
... | yes _ = max
... | no _ = n

postulate maximumFlip : ∀ (m n : ℕ) (ns : ℕ *) → maximum (m ∷ n ∷ ns) zero ≡ maximum (n ∷ m ∷ ns) zero

-- maximumFlip =

postulate maximumCongr : ∀ (m : ℕ) (ms ns : ℕ *) → maximum ms zero ≤ maximum ns zero → maximum (m ∷ ms) zero ≤ maximum (m ∷ ns) zero
-- maximumCongr =

maximumStep : ∀ (m : ℕ) (ns : ℕ *) →
  maximum ns zero ≤ maximum (m ∷ ns) zero
maximumStep m ε = 0≤n
maximumStep m (n ∷ ns) with maximumStep m ns
... | p =
  begin≤
  maximum (n ∷ ns) zero ≤⟨ maximumCongr n ns (m ∷ ns) p ⟩
  maximum (n ∷ m ∷ ns) zero ≤≡⟨ maximumFlip n m ns ⟩
  maximum (m ∷ n ∷ ns) zero
  end≤

maximumLemma : ∀ {n} {ns} → n ∈ ns → n ≤ maximum ns zero
maximumLemma {.n} {n ∷ ns} here with maximum ns zero
... | max with n ≤? max
... | yes p = p
... | no _ = n≤n n
maximumLemma {n} {m ∷ ns} (there n∈ns) with maximumLemma {n} {ns} n∈ns
... | p = trans-≤ p (maximumStep m ns)

-- simultaneous valuation update;
-- the last update is the important one
infixl 300 _l[_↦_]
_l[_↦_] : ∀ {ℓ m} {A : Set ℓ} {B : Set m} → {{Eq A}} → (A → B) → A * → B * → A → B
ρ l[ ε ↦ _ ] = ρ
ρ l[ _ ↦ ε ] = ρ
ρ l[ x ∷ xs ↦ a ∷ as ] = ρ l[ xs ↦ as ] [ x ↦ a ]

Agree : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f g : A → B) (as : A *) → Set ℓ
Agree f g as = ∀[ a ∈ as ] f a ≡ g a

map-Agree : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f g : A → B) (as : A *) →
  Agree f g as →
  map f as ≡ map g as
map-Agree {A = A} f g as agree = listEqPrinciple _ _ len memb where

  len : length (map f as) ≡ length (map g as)
  len rewrite (map-length f as) | sym (map-length g as) = refl

  memb : ∀ a k → a ∈ (map f as) ! k → a ∈ (map g as) ! k
  memb fa k a∈mapf = fa∈mapg  where

    have : ∃[ a ] a ∈ as ! k × fa ≡ f a
    have = map-∈!-inv fa f as k a∈mapf

    a : A
    a = dfst have
    
    a∈as!k : a ∈ as ! k
    a∈as!k = fst (dsnd have)

    fa≡fa : fa ≡ f a
    fa≡fa = snd (dsnd have)

    fa≡ga : f a ≡ g a
    fa≡ga = agree (∈!→∈ _ _ _ a∈as!k)

    fa∈mapg : fa ∈ map g as ! k
    fa∈mapg rewrite fa≡fa | fa≡ga = map-∈! _ _ _ _ a∈as!k

AgreeUpdate : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} (ρ τ : A → B) → (xs : A *) → Agree ρ (τ l[ xs ↦ map ρ xs ]) xs
AgreeUpdate ρ τ ε ()
AgreeUpdate ρ τ (x ∷ xs) here
  with x ≡? x
... | yes refl = refl
... | no (x≢x) = x≢x-elim x≢x
AgreeUpdate ρ τ (x ∷ xs) {a} (there a∈xs)
  with AgreeUpdate ρ τ xs {a} a∈xs
... | ρa≡τ[xs↦mapρxs]a with x ≡? a
... | yes refl = refl
... | no (x≢x) = ρa≡τ[xs↦mapρxs]a

Agree-∘ : ∀ {ℓ m o} {A : Set ℓ} {B : Set m} {C : Set o} {{_ : Eq A}} (f : B → C) (g h : A → B) → (as : A *) → Agree g h as → Agree (f ∘ g) (f ∘ h) as
Agree-∘ f g h as agree a∈as = cong f (agree a∈as)

Agree2-∘ : ∀ {ℓ m o} {A : Set ℓ} {B : Set m} {C : Set o} {{_ : Eq A}} (f : A → B → C) (g h : A → B) → (as : A *) → Agree g h as → Agree (λ a → f a (g a)) (λ a → f a (h a)) as
Agree2-∘ f g h as agree {a} a∈as = cong (f a) (agree a∈as)

sym-Agree : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {ρ τ : A → B} {xs : A *} → Agree ρ τ xs → Agree τ ρ xs
sym-Agree = {!   !}

refl-Agree : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {ρ τ : A → B} {as : A *} → Agree ρ ρ as
refl-Agree _ = refl

Agree-update-~∈ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {ρ : A → B} {a : A} {as : A *} {b : B} →
  a ~∈ as →
  Agree ρ (ρ [ a ↦ b ]) as
Agree-update-~∈ {a = a} a~∈as {a'} a'∈as
  with a ≡? a'
... | yes refl = F-elim (a~∈as a'∈as)
... | no a≢a' = refl
```

## Sublist

```
infixl 20 _⊆_
_⊆_ : ∀ {ℓ} {A : Set ℓ} → A * → A * → Set ℓ
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

ε⊆ : ∀ {ℓ} {A : Set ℓ} {as : A *} → ε ⊆ as
ε⊆ = {!   !}

⊆ε→≡ε : ∀ {ℓ} {A : Set ℓ} {as : A *} → as ⊆ ε → as ≡ ε
⊆ε→≡ε {as = ε} as⊆ε = refl
⊆ε→≡ε {as = a ∷ as} a∷as⊆ε with a∷as⊆ε here
... | ()

⊆++ : ∀ {ℓ} {A : Set ℓ} {as bs cs : A *} → as ⊆ cs → bs ⊆ cs → as ++ bs ⊆ cs
⊆++ {as = as} {bs} {cs} as⊆cs bs⊆cs a∈as++bs with a∈as++bs→a∈as⊎a∈bs {as = as} a∈as++bs
... | left a∈as = as⊆cs a∈as
... | right a∈bs = bs⊆cs a∈bs

⊆-cons-2 : ∀ {ℓ} {A : Set ℓ} {as bs : A *} {a : A} → a ∷ as ⊆ bs → as ⊆ bs
⊆-cons-2 = {!!}

⊆-++-left : ∀ {ℓ} {A : Set ℓ} {as bs : A *} → as ⊆ as ++ bs
⊆-++-left = {!!}

-- for some reason it cannot infer "as"
⊆-++-right : ∀ {ℓ} {A : Set ℓ} (as : A *) {bs : A *} → bs ⊆ as ++ bs
⊆-++-right as b∈bs = ∈→∈++-right as b∈bs

⊆++-1 : ∀ {ℓ} {A : Set ℓ} {as bs cs : A *} → as ++ bs ⊆ cs → as ⊆ cs
⊆++-1 = {!   !}

⊆++-2 : ∀ {ℓ} {A : Set ℓ} {as bs cs : A *} → as ++ bs ⊆ cs → bs ⊆ cs
⊆++-2 = {!   !}

⊆-remove : ∀ {ℓ} {A : Set ℓ} {as bs : A *} {a : A} {{_ : Eq A}} → remove a as ⊆ bs → as ⊆ (a ∷ bs)
⊆-remove = {!   !}

⊆-~∈-remove : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} {a : A} → as ⊆ bs → a ~∈ as → as ⊆ remove a bs
⊆-~∈-remove = {!!}

refl-⊆ : ∀ {ℓ} {A : Set ℓ} {as : A *} → as ⊆ as
refl-⊆ = {!   !}

trans-⊆ : ∀ {ℓ} {A : Set ℓ} {as bs cs : A *} → as ⊆ bs → bs ⊆ cs → as ⊆ cs
trans-⊆ = {!   !}

infix  1 begin⊆_
infixr 2 _⊆⟨⟩_ _⊆⟨_⟩_ _≡⊆⟨_⟩_
infix  3 _⊆∎

begin⊆_ : ∀ {ℓ} {A : Set ℓ} {x y : A *} → x ⊆ y → x ⊆ y
begin⊆ x⊆y = x⊆y

_⊆⟨⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A *) {y : A *} → x ⊆ y → x ⊆ y
_ ⊆⟨⟩ x⊆y = x⊆y

_⊆⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A *) {y z : A *} → x ⊆ y → y ⊆ z → x ⊆ z
_ ⊆⟨ x⊆y ⟩ y⊆z = trans-⊆ x⊆y y⊆z

_≡⊆⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (x : A *) {y z : A *} → x ≡ y → y ⊆ z → x ⊆ z
_ ≡⊆⟨ refl ⟩ y⊆z = y⊆z

_⊆∎ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (x : A *) → x ⊆ x
x ⊆∎ = refl-⊆

Agree-⊆ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {ρ τ : A → B} {as bs : A *} →
  Agree ρ τ bs →
  as ⊆ bs →
  Agree ρ τ as
Agree-⊆ agree as⊆bs a∈as = agree (as⊆bs a∈as)

_≈_ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as bs : A *) → Set ℓ
as ≈ bs = as ⊆ bs × bs ⊆ as

infix 30 _∩_
_∩_ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} → A * → A * → A *
ε ∩ _ = ε
(a ∷ as) ∩ bs with a ∈? bs
... | yes _ = a ∷ (as ∩ bs)
... | no _ = as ∩ bs

∈∩-Lemma1 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as bs : A *) → a ∈ as ∩ bs → a ∈ as × a ∈ bs

∈∩-Lemma1 a (a1 ∷ as) bs a∈as∩bs with a1 ∈? bs
∈∩-Lemma1 a (a ∷ as) bs here | yes a∈bs = here , a∈bs
∈∩-Lemma1 a (_ ∷ as) bs (there a∈as∩bs) | yes _
  with ∈∩-Lemma1 a as bs a∈as∩bs
... | (a∈as , a∈bs) = there a∈as , a∈bs

∈∩-Lemma1 a (a1 ∷ as) bs a∈as∩bs | no _
  with ∈∩-Lemma1 a as bs a∈as∩bs
... | (a∈as , a∈bs) = there a∈as , a∈bs

-- with a ∈? as
-- ... | yes = {!   !}
-- ... | no = {!   !}

∈∩-Lemma2 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as bs : A *) → a ∈ as → a ∈ bs → a ∈ as ∩ bs
∈∩-Lemma2 = {!   !}

-- ∩-Lemma : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {a : A} {as bs : A *} → a ∈ as ∩ bs ↔ a ∈ as × a ∈ bs
-- ∩-Lemma = ∩-Lemma1 , ∩-Lemma2

∈→∈∩ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {a : A} {as bs : A *} → a ∈ as → a ∈ as ∩ bs
∈→∈∩ = {!   !}

as⊆as∩bs : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as bs : A *) → as ⊆ as ∩ bs
as⊆as∩bs = {!!}

mon-∩-left : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs cs ds : A *} → as ⊆ bs ∩ cs → bs ⊆ ds → as ⊆ ds ∩ cs
mon-∩-left = {!!}

disjoint : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} → A * → A * → Set ℓ
disjoint as bs = ∀[ a ] (a ∈ as → a ∉ bs)

infixl 30 _\\_
_\\_ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (_ _ : A *) → A *
ε \\ bs = ε
(a ∷ as) \\ bs with a ∈? bs
... | yes _ = as \\ bs
... | no _ = a ∷ (as \\ bs)

-- ∃[ cs ] (∀[ c ] (c ∈ cs → c ∉ bs))
-- ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) (bs : A *) →  ∃[ cs ] cs ⊆ as × (∀[ a ] (a ∈ as → (a )))

-- the next two lemmas characterise \\ in terms of ∈

\\-∈ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {a : A} {as bs : A *} →
  a ∈ as →
  a ~∈ bs →
  a ∈ as \\ bs
\\-∈ = {!!}  

-- former \\-Lemma
\\-∈-inv : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as bs : A *) → ∀[ a ∈ as \\ bs ] a ∈ as × a ~∈ bs
\\-∈-inv (c ∷ as) bs a∈as\\bs
  with c ∈? bs
\\-∈-inv (c ∷ as) bs here | no c~∈bs = here , c~∈bs
\\-∈-inv (c ∷ as) bs (there a∈as\\bs) | no _
  with \\-∈-inv as bs a∈as\\bs
... | (a∈as , a~∈bs) = there a∈as , a~∈bs
\\-∈-inv (c ∷ as) bs a∈as\\bs | yes _
  with \\-∈-inv as bs a∈as\\bs
... | (a∈as , a~∈bs) = there a∈as , a~∈bs

\\-++ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as bs cs : A *) → (as ++ bs) \\ cs ≡ (as \\ cs) ++ (bs \\ cs)
\\-++ = {!   !}

\\-⊆ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} → as ⊆ bs → as \\ bs ≡ ε
\\-⊆ = {!   !}

-- TODO: can make "as" implicit, but not "bs"
\\-⊆2 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as bs : A *) → as \\ bs ⊆ as
\\-⊆2 as bs a∈as\\bs
  with \\-∈-inv as bs a∈as\\bs
... | a∈as , _ = a∈as

\\-disjoint : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} → disjoint as bs → as \\ bs ≡ as
\\-disjoint = {!   !}
```

```
-- express that all elements are distinct
distinct : ∀ {ℓ} {A : Set ℓ} → A * → Set ℓ
distinct as = ∀[ i ] ∀[ j ] ∀[ a ] (a ∈ as ! i → a ∈ as ! j → i ≡ j)

--⊆-distinct-len : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} → as ⊆ bs → distinct as → length as ≤ length bs
--⊆-distinct-len as⊆bs dst-as = {!!}
```

## List inclusion is well-founded

NOTE: The following is about *well-founded induction*
and it will be moved to some later parts.

```

-- the number of distinct elements strictly decreases
infixl 20 _⊂_
_⊂_ : ∀ {ℓ} {A : Set ℓ} → {{Eq A}} → A * → A * → Set ℓ
xs ⊂ ys = xs ⊆ ys × ~ (ys ⊆ xs)

⊂++ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs cs : A *} → as ⊂ cs → bs ⊂ cs → as ++ bs ⊂ cs
⊂++ {as = as} {bs} {cs} as⊂cs bs⊂cs = {!!}

-- a proof techniqe for strict inclusions
⊆~∈→⊂ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {a : A} {as bs : A *} →
  as ⊆ bs →
  a ~∈ as →
  a ∈ bs →
  as ⊂ bs
⊆~∈→⊂ as⊆bs a~∈as a∈bs = {!!}
```

## Remove duplicates

```
-- a.k.a. nub (except the last occurrence is kept instead of the first one)
support : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} → A * → A *
support ε = ε
support (a ∷ as) with a ∈? as
... | yes _ = support as
... | no _ = a ∷ support as

⊆-support-1 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) → as ⊆ support as
⊆-support-1 (a ∷ as) here with a ∈? as
... | yes a∈as = ⊆-support-1 as a∈as
... | no _ = here
⊆-support-1 (a ∷ as) (there {b} b∈as) with a ∈? as
... | yes _ = ⊆-support-1 as b∈as
... | no _ = there (⊆-support-1 as b∈as)

⊆-support-2 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) → support as ⊆ as
⊆-support-2 (a ∷ as) {b} b∈supas with a ∈? as
... | yes _ = there (⊆-support-2 as b∈supas)
⊆-support-2 (a ∷ as) {a} here | no _ = here
⊆-support-2 (a ∷ as) {b} (there b∈supas) | no _ = there (⊆-support-2 as b∈supas)

⊆-support-⊆-1 :  ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as bs : A *) →
  support as ⊆ support bs →
  as ⊆ bs
⊆-support-⊆-1 {a} suppas⊆suppbs a∈as = {!!}

⊆-support-⊆-2 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as bs : A *) →
  as ⊆ bs →
  support as ⊆ support bs
⊆-support-⊆-2 as bs as⊆bs a∈suppas = a∈suppbs where

  a∈as = ⊆-support-2 _ a∈suppas
  a∈bs = as⊆bs a∈as
  a∈suppbs = ⊆-support-1 _ a∈bs

distinct-support : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) → distinct (support as)
distinct-support (a ∷ as) i j b x y
  with a ∈? as
... | yes _ = distinct-support as i j b x y
distinct-support (a ∷ as) .0 .0 .a here here | no _ = refl
distinct-support (a ∷ as) 0 (suc _) a here (there y) | no a~∈as = F-elim (a~∈as (⊆-support-2 _ (∈!→∈ _ _ _ y)))
distinct-support (a ∷ as) (suc _) 0 a (there x) here | no a~∈as = F-elim (a~∈as (⊆-support-2 _ (∈!→∈ _ _ _ x)))
distinct-support (a ∷ as) (suc i) (suc j) b (there x) (there y) | no _ = cong suc (distinct-support as i j b x y)

-- more generally, support is the identity on lists without repeating elements
idempotent-support : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) →
  support (support as) ≡ support as
idempotent-support = {!!}

-- TODO
∈-remove-len : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {a : A} {as : A *}
  → a ∈ as →
  length (remove a as) < length as
∈-remove-len = {!!}

⊆-len-support1 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} →
  as ⊆ bs →
  length (support as) ≤ length bs
⊆-len-support1 {as = ε} as⊆bs = 0≤n
⊆-len-support1 {as = a ∷ as} {bs} a∷as⊆bs with a ∈? as 
... | yes _ = ⊆-len-support1 (⊆-cons-2 a∷as⊆bs)
... | no a~∈as = goal where

  ind : length (support as) ≤ length (remove a bs)
  ind = ⊆-len-support1 {as = as} {remove a bs} (⊆-~∈-remove as⊆bs a~∈as)
    where

      as⊆bs : as ⊆ bs
      as⊆bs x∈as = a∷as⊆bs (there x∈as)

  len1 : length (remove a bs) < length bs
  len1 = ∈-remove-len (a∷as⊆bs here)

  goal : length (support as) < length bs
  goal = ≤trans-< ind len1

-- TODO
-- it follows from the antisymmetry of ⊆
⊂-len-support1 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} →
  as ⊂ bs →
  length (support as) < length bs
⊂-len-support1 = {!!}

⊆-len-support : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} →
  as ⊆ bs →
  length (support as) ≤ length (support bs)
⊆-len-support {as = as} {bs} as⊆bs = ⊆-len-support1 as⊆supbs where

  as⊆supbs : as ⊆ support bs
  as⊆supbs = trans-⊆ as⊆bs (⊆-support-1 bs)

-- TODO
⊆-len-support-⊆ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} →
  as ⊆ bs →
  length (support bs) ≤ length (support as) →
  bs ⊆ as
⊆-len-support-⊆ = {!!}

⊂-len-support : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} →
  as ⊂ bs →
  length (support as) < length (support bs)
⊂-len-support {as = as} {bs} (as⊆bs , ~bs⊆as)
  with length (support as) <? length (support bs)
... | yes goal = goal
... | no ~goal = F-elim (~bs⊆as (⊆-len-support-⊆ as⊆bs (~<→≥ ~goal))) where

  lensupas≤lensupbs : length (support as) ≤ length (support bs)
  lensupas≤lensupbs = ⊆-len-support as⊆bs

~as⊂ε : ∀ {ℓ} {A : Set ℓ} {as : A *} {{_ : Eq A}} → ~ (as ⊂ ε)
~as⊂ε = {!    !}

```

## Subword embedding

```
-- noncontiguous subword embedding
infixl 9 _⊑_ _⊏_
data _⊑_ {ℓ} {A : Set ℓ} : A * → A * → Set where
  stop : ∀ {bs : A *} → ε ⊑ bs
  match : ∀ {a : A} {as bs : A *} → as ⊑ bs → a ∷ as ⊑ a ∷ bs
  skip : ∀ {a : A} {as bs : A *} → as ⊑ bs → as ⊑ a ∷ bs

refl-⊑ : ∀ {ℓ} {A : Set ℓ} {as : A *} → as ⊑ as
refl-⊑ {as = ε} = stop
refl-⊑ {as = a ∷ as} = match refl-⊑

trans-⊑ :  ∀ {ℓ} {A : Set ℓ} {as  bs cs : A *} → as ⊑ bs → bs ⊑ cs → as ⊑ cs
trans-⊑ = {!!}

antisym-⊑ : ∀ {ℓ} {A : Set ℓ} {as bs : A *} →
  as ⊑ bs →
  bs ⊑ as →
  as ≡ bs
antisym-⊑ = {!!}

_⊏_ : ∀ {ℓ} {A : Set ℓ} → A * → A * → Set
xs ⊏ ys = xs ⊑ ys × ~ (ys ⊑ xs)

-- wf-⊏ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} → WellFounded {A = A *} _⊏_
-- wf-⊏ = {!!}
```

### Length

```
length-⊑ : ∀ {ℓ} {A : Set ℓ} {as bs : A *} →
  as ⊑ bs →
  length as ≤ length bs
length-⊑ stop = 0≤n
length-⊑ (match as⊑bs) = s≤s (length-⊑ as⊑bs)
length-⊑ (skip as⊑bs) = trans-≤ n≤sucn (s≤s (length-⊑ as⊑bs))

length-⊑-≡ : ∀ {ℓ} {A : Set ℓ} {as bs : A *} →
  as ⊑ bs →
  length as ≥ length bs →
  as ≡ bs
length-⊑-≡ = {!!}

length-⊏ : ∀ {ℓ} {A : Set ℓ} {as bs : A *} →
  as ⊏ bs →
  length as < length bs
length-⊏ {as = as} {bs} (as⊑bs , ~bs⊑as) = lenas<lenbs where

  lenas≤lenbs : length as ≤ length bs
  lenas≤lenbs = length-⊑ as⊑bs

  lenas≢lenbs : length as ≢ length bs
  lenas≢lenbs lenas=lenbs = ~bs⊑as bs⊑as where

    as≡bs : as ≡ bs
    as≡bs = length-⊑-≡ as⊑bs lenas≥lenbs where

      lenas≥lenbs : length as ≥ length bs
      lenas≥lenbs rewrite sym lenas=lenbs = refl-≤
        
    bs⊑as : bs ⊑ as
    bs⊑as rewrite as≡bs = refl-⊑

  lenas<lenbs : length as < length bs
  lenas<lenbs = ≤×≢→< lenas≤lenbs lenas≢lenbs
```

### Append

```
-- in fact it follows from a more general congruence property
++-⊑ : ∀ {ℓ} {A : Set ℓ} {as bs : A *} (cs : A *) →
  as ⊑ bs →
  cs ++ as ⊑ cs ++ bs
++-⊑ = {!!}

++-⊑2 : ∀ {ℓ} {A : Set ℓ} {as bs : A *} (cs : A *) →
  as ⊑ bs →
  as ⊑ cs ++ bs
++-⊑2 = {!!}
```

### Map

```
map-⊑ : ∀ {ℓ m} {A : Set ℓ} {B : Set m}
  (f : A → B)
  (as bs : A *) →
  as ⊑ bs →
  map f as ⊑ map f bs
map-⊑ f ε bs stop = stop
map-⊑ f (_ ∷ as) (_ ∷ bs) (match as⊑bs)
  with map-⊑ f as bs as⊑bs
... | ind = match ind
-- no idea why it is greyed out below
map-⊑ f as (b ∷ bs) (skip {b} {as} {bs} as⊑bs)
 with map-⊑ f as bs as⊑bs
... | ind = skip ind

map-⊆ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B) (as bs : A *) →
  as ⊆ bs → map f as ⊆ map f bs
map-⊆ = {!!}

map-\\-⊆ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {{_ : Eq B}} (f : A → B) (as bs : A *) →
  map f (as \\ bs) ⊆ map f as
map-\\-⊆ f as bs {b} b∈mapfas\\bs
  with map-∈-inv f b∈mapfas\\bs
... | a , a∈as\\bs , b≡fa
  with \\-⊆2 as bs a∈as\\bs
... | a∈as rewrite b≡fa = map-∈ f a∈as
```

### Filter

```
filter-⊑ : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} →
  (P? : Decidable P) →
  (as : A *) →
  filter P? as ⊑ as  
filter-⊑ P? ε = stop
filter-⊑ P? (a ∷ as)
  with filter-⊑ P? as
... | filter⊑as
  with P? a
... | yes _ = match filter⊑as
... | no _ = skip filter⊑as

-- from the above
filter-⊆ : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} {{_ : Eq A}} →
  (P? : Decidable P) →
  (as : A *) →
  filter P? as ⊆ as  
filter-⊆ P? as = {!!}

filter-⊏ : ∀ {ℓ m} {A : Set ℓ} {P : A → Set m} →
  (P? : Decidable P) →
  (as : A *) →
  ∃[ a ∈ as ] ~ P a →
  filter P? as ⊏ as
filter-⊏ = {!!}
  
remove-⊑ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as : A *) → remove a as ⊑ as
remove-⊑ a as = filter-⊑ (λ b → ~? (b ≡? a)) as

-- from the above
remove-⊆ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as : A *) → remove a as ⊆ as
remove-⊆ a as = {!!}

remove-⊏ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}}
  (a : A) (as : A *) →
  a ∈ as →
  remove a as ⊏ as
remove-⊏ a as a∈as =  filter-⊏ (λ b → ~? (b ≡? a)) as (a , a∈as , ~~a≡a) where

  ~~a≡a : ~ ~ (a ≡ a)
  ~~a≡a ~a≡a = ~a≡a refl
```

### Concatenation

```
concat-∷ : ∀ {ℓ} {A : Set ℓ} (as : A *) (ass : A * *) →
  concat (as ∷ ass) ≡ as ++ concat ass
concat-∷ = {!!}

concat-∈ : ∀ {ℓ} {A : Set ℓ} (a : A) (ass : A * *) →
  a ∈ concat ass →
  ∃[ as ∈ ass ] a ∈ as
concat-∈ a ass = {!!}

concat-∈2 : ∀ {ℓ} {A : Set ℓ} (a : A) (as : A *) (ass : A * *) →
  a ∈ as →
  as ∈ ass →
  a ∈ concat ass
concat-∈2 a as (as ∷ ass) a∈as here
  rewrite concat-∷ as ass = ∈→∈++-left (concat ass) a∈as
concat-∈2 a as (bs ∷ ass) a∈as (there as∈ass)
  rewrite concat-∷ bs ass
  with concat-∈2 a as ass a∈as as∈ass
... | a∈concatass = ∈→∈++-right bs a∈concatass

concat-++ : ∀ {ℓ} {A : Set ℓ} (ass bss : A * *) →
  concat (ass ++ bss) ≡ concat ass ++ concat bss
concat-++ ass bss = {!!}

concat-⊑ : ∀ {ℓ} {A : Set ℓ} (ass bss : A * *) →
  ass ⊑ bss →
  concat ass ⊑ concat bss
concat-⊑ ε bss stop = stop
concat-⊑ (as ∷ ass) (as ∷ bss) (match ass⊑bss)
  with concat-⊑ ass bss ass⊑bss
... | ind
  rewrite concat-∷ as ass |
          concat-∷ as bss = ++-⊑ as ind 
concat-⊑ ass (bs ∷ bss) (skip ass⊑bss)
  with concat-⊑ ass bss ass⊑bss
... | ind
  rewrite concat-∷ bs bss = ++-⊑2 bs ind
```

### concatMap

```
concatMap-⊑ : ∀ {ℓ m} {A : Set ℓ} {B : Set m}
  (f : A → B *)
  (as bs : A *) →
  as ⊑ bs →
  concatMap f as ⊑ concatMap f bs
concatMap-⊑ f as bs as⊑bs = goal where

  have : map f as ⊑ map f bs
  have = map-⊑ f as bs as⊑bs

  goal : concatMap f as ⊑ concatMap f bs
  goal = concat-⊑ _ _ have

concatMap-++ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B *) (as bs : A *) →
  concatMap f (as ++ bs) ≡ concatMap f as ++ concatMap f bs
concatMap-++ f as bs rewrite sym (map-++ f as bs) = concat-++ (map f as) (map f bs)

concatMap-∈ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B *) (a : A) (as : A *) (b : B) →
  a ∈ as →
  b ∈ f a →
  b ∈ concatMap f as 
concatMap-∈ f a as b a∈as b∈fa = b∈cMfas where

  fa∈mapfas : f a ∈ map f as
  fa∈mapfas = map-∈ f a∈as
  
  b∈cMfas : b ∈ concat (map f as)
  b∈cMfas = concat-∈2 _ _ _ b∈fa fa∈mapfas

concatMap-∈-inv : ∀ {ℓ m} {A : Set ℓ} {B : Set m} (f : A → B *) (as : A *) (b : B) →
  b ∈ concatMap f as →
  ∃[ a ∈ as ] b ∈ f a
concatMap-∈-inv f as b b∈cMas
  with concat-∈ b (map f as) b∈cMas
... | bs , bs∈mapfas , b∈bs
  with map-∈-inv f bs∈mapfas
... | a , a∈as , bs≡fa  = a , a∈as , b∈fa where

  b∈fa : b ∈ f a
  b∈fa rewrite sym bs≡fa = b∈bs

concatMap-\\ : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {{_ : Eq B}} (f : A → B *) (as bs : A *) →
  concatMap f (as \\ bs) ⊆ concatMap f as
concatMap-\\ f as bs {b} b∈cMfas\\bs
  with concatMap-∈-inv f (as \\ bs) b b∈cMfas\\bs
... | a , a∈as\\bs , b∈fa
  with \\-⊆2 as bs a∈as\\bs
... | a∈as = concatMap-∈ f a as b a∈as b∈fa

-- wrong
--concatMap-\\-2 : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {{_ : Eq A}} {{_ : Eq B}} (f : A → B *) (as bs : A *) →
--  ∀[ c ∈ concatMap f (as \\ bs) ] c ~∈ concatMap f bs
--concatMap-\\-2 f as bs  = {!!}

```

## Membership

```
⊑-∈ : ∀ {ℓ} {A : Set ℓ} {a : A} {as bs : A *} →
  a ∈ as →
  as ⊑ bs →
  a ∈ bs
⊑-∈ here (match as⊑bs) = here
⊑-∈ (there a∈as) (match as⊑bs)
  with ⊑-∈ a∈as as⊑bs
... | a∈bs = there a∈bs
⊑-∈ a∈as (skip as⊑bs)
  with ⊑-∈ a∈as as⊑bs
... | a∈bs = there a∈bs

--  with ⊑-∈ a∈as as⊑bs
--... | x = ?
```

## Support

```
support-⊑-1 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) → support as ⊑ as
support-⊑-1 = {!!}

support-⊑-2 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (as : A *) → as ⊑ support as
support-⊑-2 = {!!}

support-⊑ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {as bs : A *} → as ⊑ bs → support as ⊑ support bs
support-⊑ = {!!}
```

## Provable first occurrences

Consider replacing `_∈_` with `_∈1_` everywhere?

```
infix 5 _∈1_ _∈1?_
data _∈1_ {ℓ} {A : Set ℓ} : A → A * → Set ℓ where
    here : ∀ {x} {xs : A *} → x ∈1 (x ∷ xs)
    there : ∀ {x y} {xs : A *} → x ≢ y → x ∈1 xs → x ∈1 (y ∷ xs)

_∈1?_ : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} (a : A) (as : A *) → Dec (a ∈1 as)
a ∈1? ε = no (λ ())
a ∈1? b ∷ as with a ≡? b
... | yes refl = yes (here)
... | no a≢b with a ∈1? as
... | yes a∈1as = yes (there a≢b a∈1as)
... | no ~a∈1as = no (goal) where
  goal : ~ (a ∈1 b ∷ as)
  goal here = a≢b refl
  goal (there _ a∈1as) = ~a∈1as a∈1as

∈1→∈ : ∀ {ℓ} {A : Set ℓ} {a : A} {as : A *} → a ∈1 as → a ∈ as
∈1→∈ here = here
∈1→∈ (there _ a∈1as) = there (∈1→∈ a∈1as)

∈→∈1 : ∀ {ℓ} {A : Set ℓ} {{_ : Eq A}} {a : A} {as : A *} → a ∈ as → a ∈1 as
∈→∈1 {a = a} {a ∷ _} here = here
∈→∈1 {a = a} {b ∷ as} (there a∈as) with a ≡? b
... | yes refl = here
... | no a≢b = there a≢b (∈→∈1 a∈as)
```

```
-- move this to List
data Perm {ℓ} {A : Set ℓ} : A * → A * → Set ℓ where
  stop : ∀ {as} → Perm as as
  skip : ∀ {a as bs} → Perm as bs → Perm (a ∷ as) (a ∷ bs)
  swap : ∀ {a b as bs} → Perm as bs → Perm (a ∷ b ∷ as) (b ∷ a ∷ bs)
  tran : ∀ {as bs cs} → Perm as bs → Perm bs cs → Perm as cs

-- _∼_ : ∀ {ℓ} {A : Set ℓ} → A * → A * → Set ℓ
-- as ∼ bs = Perm as bs

perm-sym : ∀ {ℓ} {A : Set ℓ} {as bs : A *} → Perm as bs → Perm bs as
perm-sym perm = {!!}
```
