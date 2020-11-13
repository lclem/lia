---
title: Trees
---

In this chapter we study labelled unranked trees.

For the moment, this is only used to decide equality of formulas.

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.Tree where
open import part0.utils
open import part0.nat
open import part0.fun
open import part0.eq
open import part0.logic
open import part0.decidable
open import part0.list
open import Agda.Primitive

variable

  ℓ : Level
  A : Set ℓ

  a a' : A
  as as' : A *

data Tree {ℓ} (A : Set ℓ) : Set ℓ where
    Nil : Tree A
    Node : A → Tree A * → Tree A
```

## Injectivity of constructors

```
Node-inj-left : Node a as ≡ Node a' as' → a ≡ a'
Node-inj-left refl = refl

Node-inj-right : Node a as ≡ Node a' as' → as ≡ as'
Node-inj-right refl = refl
```



# Decidable equality

Equality on `Tree A` is decidable
provided it is decidable on `A`.

```
instance
  eqTree : ∀ {ℓ} {A : Set ℓ} → {{Eq A}} → Eq (Tree A)
  _≡?_ {{eqTree}} = go where

    go : ∀ s t → Dec (s ≡ t)
    go* : ∀ as bs → Dec (as ≡ bs)

    go Nil Nil = yes {proof = refl}
    go Nil (Node _ _) = no {proof = λ ()}
    go (Node _ _) Nil = no {proof = λ ()}
    go (Node a as) (Node b bs)
      with a ≡? b
    ... | no {a≢b} = no {proof = λ{ refl → ¬x≢x a≢b}}
    ... | yes {refl}
      with go* as bs
    ... | no {as≢bs} = no {proof = λ{ refl → ¬x≢x as≢bs}}
    ... | yes {refl}= yes {proof = refl}

    -- need an extra case analysis to satisfy the termination checker
    -- (essentially reproving decidability of list equality);
    -- alternative: define "go" by well-founded induction on the size of the tree...
    go* ε ε = yes {proof = refl}
    go* ε (_ ∷ _) = no {proof = λ ()}
    go* (_ ∷ _) ε = no {proof = λ ()}
    go* (a ∷ as) (b ∷ bs)
      with a ≡? b
    ... | no {a≢b} = no {proof = λ{ refl → ¬x≢x a≢b}}
    ... | yes {refl}
      with go* as bs
    ... | no {as≢bs} = no {proof = λ{ refl → ¬x≢x as≢bs}}
    ... | yes {refl}= yes {proof = refl}
```
