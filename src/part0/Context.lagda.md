---
title: Context
---

```
module part0.Context where
open import part0.nat
open import part0.Fin
open import part0.vector
open import part0.logic

-- Generalised context with named holes
data Ctx (n : ℕ) : Set where
  □ : Fin n → Ctx n
  Num : ℕ → Ctx n
  Suc : Ctx n → Ctx n
  _+C_ : Ctx n → Ctx n → Ctx n
  _*C_ : Ctx n → Ctx n → Ctx n

-- replace the hole with a given formula
ctxApply : ∀ {n} → Ctx n → Vector AExp n → AExp
ctxApply (□ k) es = es ! k
ctxApply (Num n) _ = Num n
ctxApply (Suc ctx) e = Suc (ctxApply ctx e)
ctxApply (ctx1 +C ctx2) e = ctxApply ctx1 e +E ctxApply ctx2 e
ctxApply (ctx1 *C ctx2) e = ctxApply ctx1 e *E ctxApply ctx2 e

postulate cong2-≤ : ∀ {a b c d} → (ctx : Ctx 2) → a ≤ b → c ≤ d → A⟦ ctxApply ctx < Num a , Num c > ⟧ ≤ A⟦ ctxApply ctx < Num b , Num d > ⟧

```
