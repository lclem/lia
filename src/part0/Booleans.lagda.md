---
title: Boolean values🚧
---


```
{-# OPTIONS --rewriting --confluence-check  #-}

module part0.Booleans where
open import part0.Equality public
```

In this section we introduce *Boolean values*.

```
data 𝔹 : Set where
  ff : 𝔹
  tt : 𝔹
```

Erasure:

⌊_⌋
```
⌞_⌟ : ∀ {ℓ} {A : Set ℓ} → Dec A → 𝔹
⌞ yes _ ⌟ = tt
⌞ no _ ⌟ = ff
```

```
tt≢ff : tt ≢ ff
tt≢ff ()

ff≢tt : ff ≢ tt
ff≢tt ()

ff≢tt-elim : ff ≡ tt → whatever
ff≢tt-elim ff≡tt = F-elim (ff≢tt ff≡tt)

a≡ff→a≡tt-elim : ∀ {a} → a ≡ ff → a ≡ tt → whatever
a≡ff→a≡tt-elim refl ()
```

## Equality

```
instance
  Eq𝔹 : Eq 𝔹
  _≡?_ {{Eq𝔹}} = go where

    go : ∀ b c → Dec (b ≡ c)
    go tt tt = yes refl
    go tt ff = no (λ ())
    go ff tt = no (λ ())
    go ff ff = yes refl
```

## Truth tables

```
infix 100 ¬𝔹_
infixl 99 _∧𝔹_
infixl 98 _∨𝔹_ _⇒𝔹_
infixl 97 _⇔𝔹_

_∧𝔹_ : 𝔹 → 𝔹 → 𝔹
ff ∧𝔹 _ = ff
_ ∧𝔹 ff = ff
tt ∧𝔹 tt = tt

_∨𝔹_ : 𝔹 → 𝔹 → 𝔹
tt ∨𝔹 _ = tt
_ ∨𝔹 tt = tt
ff ∨𝔹 ff = ff

¬𝔹_ : 𝔹 → 𝔹
¬𝔹 tt = ff
¬𝔹 ff = tt

_⇒𝔹_ : 𝔹 → 𝔹 → 𝔹
ff ⇒𝔹 _ = tt
_ ⇒𝔹 tt = tt
tt ⇒𝔹 ff = ff

_⇔𝔹_ : 𝔹 → 𝔹 → 𝔹
tt ⇔𝔹 tt = tt
ff ⇔𝔹 ff = tt
_ ⇔𝔹 _ = ff
```

## Short-circuit evaluation

The current definitions do not need to look at the second argument for certain values of the first argument.
The we add the following rewrite directives
in order to allow short-circuit evaluation even w.r.t. the second argument.

```
∨𝔹-rewrite : ∀ a → a ∨𝔹 tt ≡ tt
∨𝔹-rewrite tt = refl
∨𝔹-rewrite ff = refl

{-# REWRITE ∨𝔹-rewrite #-}

∨𝔹-rewrite-ff : ∀ a → ff ∨𝔹 a ≡ a
∨𝔹-rewrite-ff tt = refl
∨𝔹-rewrite-ff ff = refl

{-# REWRITE ∨𝔹-rewrite-ff #-}

∧𝔹-rewrite : ∀ a → a ∧𝔹 ff ≡ ff
∧𝔹-rewrite tt = refl
∧𝔹-rewrite ff = refl

∧𝔹-rewrite2 : ∀ a → a ∧𝔹 tt ≡ a
∧𝔹-rewrite2 tt = refl
∧𝔹-rewrite2 ff = refl

{-# REWRITE ∧𝔹-rewrite ∧𝔹-rewrite2 #-}

⇒𝔹-rewrite-tt : ∀ a → tt ⇒𝔹 a ≡ a
⇒𝔹-rewrite-tt tt = refl
⇒𝔹-rewrite-tt ff = refl

{-# REWRITE ⇒𝔹-rewrite-tt #-}

```

## Inter-definability

```
semantics⇒𝔹 : ∀ a b → a ⇒𝔹 b ≡ ¬𝔹 a ∨𝔹 b
semantics⇒𝔹 tt tt = refl
semantics⇒𝔹 tt ff = refl
semantics⇒𝔹 ff tt = refl
semantics⇒𝔹 ff ff = refl

semantics⇔𝔹 : ∀ a b → a ⇔𝔹 b ≡ (¬𝔹 a ∨𝔹 b) ∧𝔹 (a ∨𝔹 ¬𝔹 b)
semantics⇔𝔹 tt tt = refl
semantics⇔𝔹 tt ff = refl
semantics⇔𝔹 ff tt = refl
semantics⇔𝔹 ff ff = refl

-- ⇒→⇔𝔹 : ∀ a b → a ⇔𝔹 b ≡ (a ⇒𝔹 b) ∧𝔹 (b ⇒𝔹 a)
-- ⇒→⇔𝔹 = {!!}

semantics¬⇒𝔹 : ∀ a b → ¬𝔹 (a ⇒𝔹 b) ≡ a ∧𝔹 ¬𝔹 b
semantics¬⇒𝔹 tt tt = refl
semantics¬⇒𝔹 tt ff = refl
semantics¬⇒𝔹 ff tt = refl
semantics¬⇒𝔹 ff ff = refl

semantics¬⇔𝔹 : ∀ a b → ¬𝔹 (a ⇔𝔹 b) ≡ a ∧𝔹 ¬𝔹 b ∨𝔹 ¬𝔹 a ∧𝔹 b
semantics¬⇔𝔹 tt tt = refl
semantics¬⇔𝔹 tt ff = refl
semantics¬⇔𝔹 ff tt = refl
semantics¬⇔𝔹 ff ff = refl

push¬⇔𝔹 : ∀ a b → ¬𝔹 (a ⇔𝔹 b) ≡ ¬𝔹 a ⇔𝔹 b
push¬⇔𝔹 tt tt = refl
push¬⇔𝔹 tt ff = refl
push¬⇔𝔹 ff tt = refl
push¬⇔𝔹 ff ff = refl
```

## Basic properties

### Associativity

```
assoc-∨𝔹 : ∀ a b c → a ∨𝔹 b ∨𝔹 c ≡ a ∨𝔹 (b ∨𝔹 c)
assoc-∨𝔹 tt tt tt = refl
assoc-∨𝔹 tt tt ff = refl
assoc-∨𝔹 tt ff tt = refl
assoc-∨𝔹 tt ff ff = refl
assoc-∨𝔹 ff tt tt = refl
assoc-∨𝔹 ff tt ff = refl
assoc-∨𝔹 ff ff tt = refl
assoc-∨𝔹 ff ff ff = refl
```

```
assoc-∧𝔹 : ∀ a b c → a ∧𝔹 b ∧𝔹 c ≡ a ∧𝔹 (b ∧𝔹 c)
assoc-∧𝔹 tt tt tt = refl
assoc-∧𝔹 tt tt ff = refl
assoc-∧𝔹 tt ff tt = refl
assoc-∧𝔹 tt ff ff = refl
assoc-∧𝔹 ff tt tt = refl
assoc-∧𝔹 ff tt ff = refl
assoc-∧𝔹 ff ff tt = refl
assoc-∧𝔹 ff ff ff = refl
```

### Distributivity

```
distr-left-∧∨𝔹 : ∀ a b c → a ∧𝔹 (b ∨𝔹 c) ≡ a ∧𝔹 b ∨𝔹 a ∧𝔹 c
distr-left-∧∨𝔹 tt tt tt = refl
distr-left-∧∨𝔹 tt tt ff = refl
distr-left-∧∨𝔹 tt ff tt = refl
distr-left-∧∨𝔹 tt ff ff = refl
distr-left-∧∨𝔹 ff tt tt = refl
distr-left-∧∨𝔹 ff tt ff = refl
distr-left-∧∨𝔹 ff ff tt = refl
distr-left-∧∨𝔹 ff ff ff = refl

distr-right-∧∨𝔹 : ∀ a b c → (a ∨𝔹 b) ∧𝔹 c ≡ a ∧𝔹 c ∨𝔹 b ∧𝔹 c
distr-right-∧∨𝔹 tt tt tt = refl
distr-right-∧∨𝔹 tt tt ff = refl
distr-right-∧∨𝔹 tt ff tt = refl
distr-right-∧∨𝔹 tt ff ff = refl
distr-right-∧∨𝔹 ff tt tt = refl
distr-right-∧∨𝔹 ff tt ff = refl
distr-right-∧∨𝔹 ff ff tt = refl
distr-right-∧∨𝔹 ff ff ff = refl
```

### Conjunctive property

```
𝔹conjProp1 : ∀ a b → a ∧𝔹 b ≡ tt → a ≡ tt
𝔹conjProp1 tt tt refl = refl

𝔹conjProp2 : ∀ a b → a ∧𝔹 b ≡ tt → b ≡ tt
𝔹conjProp2 tt tt refl = refl

𝔹conjProp3 : ∀ a b → a ≡ tt → b ≡ tt → a ∧𝔹 b ≡ tt
𝔹conjProp3 tt tt refl refl = refl

∧𝔹-inv : ∀ a b →  a ∧𝔹 b ≡ tt → a ≡ tt × b ≡ tt
∧𝔹-inv tt tt refl = refl , refl
```

### Disjunctive property

```
𝔹disjProp1 : ∀ a b → a ≡ tt → a ∨𝔹 b ≡ tt 
𝔹disjProp1 tt _ refl = refl

-- shortened thanks to REWRITE
𝔹disjProp2 : ∀ a b → b ≡ tt → a ∨𝔹 b ≡ tt
𝔹disjProp2 _ _ refl = refl
--𝔹disjProp2 tt tt refl = refl
--𝔹disjProp2 ff tt refl = refl

𝔹disjProp3 : ∀ a b → a ≡ ff → b ≡ ff → a ∨𝔹 b ≡ ff
𝔹disjProp3 ff ff refl refl = refl

∨𝔹-inv : ∀ a b → a ∨𝔹 b ≡ tt → a ≡ tt ⊎ b ≡ tt
∨𝔹-inv tt _ refl = left refl
∨𝔹-inv ff tt refl = right refl
```

### Implication

```
𝔹implProp1 : ∀ a b → a ≡ ff → a ⇒𝔹 b ≡ tt
𝔹implProp1 ff tt refl = refl
𝔹implProp1 ff ff refl = refl

𝔹implProp2 : ∀ a b → a ≡ tt → a ⇒𝔹 b ≡ b
𝔹implProp2 tt tt refl = refl
𝔹implProp2 tt ff refl = refl

⇒𝔹-inv : ∀ a b → a ⇒𝔹 b ≡ tt → a ≡ ff ⊎ b ≡ tt
⇒𝔹-inv tt tt refl = right refl
⇒𝔹-inv ff tt refl = left refl
⇒𝔹-inv ff ff refl = left refl
```

### Negation

```
¬𝔹-inv : ∀ a → ¬𝔹 a ≡ tt → a ≡ ff
¬𝔹-inv ff refl = refl

¬𝔹-prop : ∀ a → ¬𝔹 a ≡ tt → a ⇒𝔹 ff ≡ tt
¬𝔹-prop ff refl = refl
```

### Bi-implication

```
⇔𝔹-inv : ∀ a b → a ⇔𝔹 b ≡ tt → a ≡ tt × b ≡ tt ⊎ a ≡ ff × b ≡ ff
⇔𝔹-inv tt tt refl = left (refl , refl)
⇔𝔹-inv ff ff refl = right (refl , refl)

⇔→⇒𝔹1 : ∀ a b → a ⇔𝔹 b ≡ tt → a ⇒𝔹 b ≡ tt
⇔→⇒𝔹1 tt tt refl = refl
⇔→⇒𝔹1 ff ff refl = refl

⇔→⇒𝔹2 : ∀ a b → a ⇔𝔹 b ≡ tt → b ⇒𝔹 a ≡ tt
⇔→⇒𝔹2 tt tt refl = refl
⇔→⇒𝔹2 ff ff refl = refl
```

## Order

```
data _≤𝔹_ : 𝔹 → 𝔹 → Set where
  ff≤ff : ff ≤𝔹 ff
  ff≤tt : ff ≤𝔹 tt
  tt≤tt : tt ≤𝔹 tt

~tt≤𝔹ff : ~ (tt ≤𝔹 ff)
~tt≤𝔹ff ()

tt≤𝔹ff-elim : tt ≤𝔹 ff → whatever
tt≤𝔹ff-elim tt≤ff = F-elim (~tt≤𝔹ff tt≤ff)
```

### Monotonicity

```
monotone-∧𝔹 : ∀ {a b c d} →
  a ≤𝔹 b →
  c ≤𝔹 d →
  -----------------
  a ∧𝔹 c ≤𝔹 b ∧𝔹 d
  
monotone-∧𝔹 ff≤ff _ = ff≤ff
monotone-∧𝔹 ff≤tt ff≤ff = ff≤ff
monotone-∧𝔹 ff≤tt ff≤tt = ff≤tt
monotone-∧𝔹 ff≤tt tt≤tt = ff≤tt
monotone-∧𝔹 tt≤tt ff≤ff = ff≤ff
monotone-∧𝔹 tt≤tt ff≤tt = ff≤tt
monotone-∧𝔹 tt≤tt tt≤tt = tt≤tt
```

```
monotone-∨𝔹 : ∀ {a b c d} →
  a ≤𝔹 b →
  c ≤𝔹 d →
  -----------------
  a ∨𝔹 c ≤𝔹 b ∨𝔹 d
  
monotone-∨𝔹 ff≤ff ff≤ff = ff≤ff
monotone-∨𝔹 ff≤ff ff≤tt = ff≤tt
monotone-∨𝔹 ff≤ff tt≤tt = tt≤tt
monotone-∨𝔹 ff≤tt ff≤ff = ff≤tt
monotone-∨𝔹 ff≤tt ff≤tt = ff≤tt
monotone-∨𝔹 ff≤tt tt≤tt = tt≤tt 
monotone-∨𝔹 tt≤tt ff≤ff = tt≤tt
monotone-∨𝔹 tt≤tt ff≤tt = tt≤tt
monotone-∨𝔹 tt≤tt tt≤tt = tt≤tt
```

## Conditionals

```
Cond𝔹 : ∀ {ℓ} {A : Set ℓ} → A → A → 𝔹 → A
Cond𝔹 x y tt = x
Cond𝔹 x y ff = y
```
