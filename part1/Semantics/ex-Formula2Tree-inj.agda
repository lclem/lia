module part1.Semantics.ex-Formula2Tree-inj where

open import part0.index

postulate n' : ℕ
  
open import part1.Semantics n' hiding (Formula2Tree-inj)

Formula2Tree-inj : Injective Formula2Tree
Formula2Tree-inj = a-test-o3