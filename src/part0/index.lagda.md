---
title: "Part 0: Basic programming in Agda 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.index where
open import part0.Utils public
open import part0.Equality public
open import part0.Logic public
open import part0.Decidable public
open import part0.Booleans public
open import part0.List public
open import part0.Permutations public
open import part0.TList public
open import part0.Finite public
open import part0.Enumerable public
open import part0.Tree public
```

<executable-pre data-executable="true" data-language="agda">

module test where

open import part0.Naturals

variable
    ℓ m : Level
    A : Set ℓ
    B : Set m

proj1 : A → B → A
proj1 x y = x

proj2 : A → B → B
proj2 x y = ?

data Two : Set where
    one : Two
    two : Two

select : Two → A → A → A
select x a₀ a₁ = {! x !}
</executable-pre>

An example citation to [@Craig:JSL:1957]
and another to the same [@Craig:JSL:1957],
then @Craig:JSL:1957,
or even just (@Craig:JSL:1957),
finally another one [@Langford:AM:1926:B],
and then Craig again [@Craig:JSL:1957].

::: {#refs}

# References

:::
