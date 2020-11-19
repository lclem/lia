---
title: "Gentzen's sequent calculus 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas  #-}

open import part0.index

module part2.SequentCalculus (n' : ℕ) where
open import part2.NaturalDeduction n' public hiding (_⊢_)
```

# Sequents

```
infixr 5 _⊢_
data _⊢_ : Context → Context → Set where
```
