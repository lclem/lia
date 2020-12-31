---
title: "Part 1: Classical propositional logic 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}

module part1.index where

open import part1.Semantics
open import part1.CharacteristicFormulas
open import part1.NormalForms
open import part1.Hilbert
open import part1.NaturalDeduction
open import part1.SequentCalculus
--open import part1.Resolution
--open import part1.Resolution-Completeness
--open import part1.Interpolation
--open import part1.Compactness
```

* Mention the library [@Prieto-CubidesGarzonSicard-Ramirez:zenodo:2018]. Interesting points: normal forms NNF, DNF, and CNF are defined and it is shown that the normal form transformations preserve provability. In this way there is no need to resort to the semantics. In our approach, we would use soundness of the transformation (which is easier to establish) and then use the completeness theorem (which is a powerful property to have anyway).

!codemirrorCustom(test1)
~~~~
module test1 where

open import Agda.Primitive
-- BEGIN SOLUTION

variable
    ℓ m n : Level
    A : Set ℓ
    B : Set m
    C : Set n

comp : (A → B) → (B → C) → A → C
comp f g = ?
~~~~

!codemirrorCustom(test2)
~~~~
module test2 where

open import Agda.Primitive
-- BEGIN SOLUTION

variable
    ℓ m n : Level
    A : Set ℓ
    B : Set m
    C : Set n

comp : (A → B) → (B → C) → A → C
comp f g = ?
~~~~

!codemirrorCustom(test3)
~~~~
module test3 where

-- BEGIN SOLUTION

id : {A : Set} → A → A
id x = ?
~~~~

!codemirrorCustom(test4)
~~~~
module test4 where

-- BEGIN SOLUTION

id : {A : Set} → A → A
id x = ?
~~~~

!codemirrorCustom(test5)
~~~~
module test5 where

-- BEGIN SOLUTION

id : {A : Set} → A → A
id x = ?
~~~~