---
title: "Regular programs 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Reg where
open import part0.index hiding (AExp; A⟦_⟧; _*)
open import part5.Exp using (VarName; AExp; BExp; ¬_; B⟦_⟧_; A⟦_⟧_)
open import part5.Imp hiding (⇒-det; ↝*-trans; _↝*⟨⟩_; _↝⟨_⟩_; _↝*⟨_⟩_)
```

```
data Reg : Set where
  ε : Reg
  _≔_ : VarName → AExp → Reg
  _?? : BExp → Reg
  _⨟_ : Reg → Reg → Reg
  _or_ : Reg → Reg → Reg
  _*  : Reg → Reg

infixr 20 _or_
infix 25 _*
infix 30 _??
```

Small-steps operational semantics:

```
private
  variable
    x : VarName
    e : AExp
    b : BExp
    s s′ s″ : State
    c c′ c″ d : Reg

infix 10 _,_⇝_
data _,_⇝_ : Reg → State → Reg × State ⊎ State → Set where

  ε : ---------------
      ε , s ⇝ right s

  assign : --------------------------------------
           x ≔ e , s ⇝ right (s [ x ↦ A⟦ e ⟧ s ])

  test : B⟦ b ⟧ s ≡ tt →
         ------------------
         b ?? , s ⇝ right s

  seq-0 : c , s ⇝ right s′ →
          -------------------------
          c ⨟ d , s ⇝ left (d , s′)

  seq-1 : c , s ⇝ left (c′ , s′) →
          -----------------------------
          c ⨟ d , s ⇝ left (c′ ⨟ d , s′)

  or-left : -------------------------
            c or d , s ⇝ left (c , s)

  or-right : -------------------------
             c or d , s ⇝ left (d , s)

  star-stop : -----------------
              c * , s ⇝ right s

  star-step : ----------------------------
              c * , s ⇝ left (c ⨟ c * , s)
```

Transitive closure:

```
infix 3 _,_⇝*_
data _,_⇝*_ : Reg → State → State → Set where

  stop : c , s ⇝ right s′ →
         ------------------
         c , s ⇝* s′

  step : c , s ⇝ left (c′ , s′) →
         c′ , s′ ⇝* s″ →
         ------------------------
         c , s ⇝* s″

infixr 10 _,,_
infix 11 _#

pattern _,,_ δ₀ δ₁ = step δ₀ δ₁
pattern _# δ = stop δ

seq-lemma : c , s ⇝* s′ →
            d , s′ ⇝* s″ →
            ---------------
            c ⨟ d , s ⇝* s″

seq-lemma (δ #) δ₁ = (seq-0 δ) ,, δ₁
seq-lemma (δ ,, δ₀) δ₁ = (seq-1 δ) ,, (seq-lemma δ₀ δ₁)

assoc-seq : c ⨟ (c′ ⨟ c″) , s ⇝* s′ →
            -----------------------
            (c ⨟ c′) ⨟ c″ , s ⇝* s′

assoc-seq = {!   !}
```

Encode imperative programs as equivalent regular programs.

```
imp2reg : Cmd → Reg
imp2reg skip = ε
imp2reg (x ≔ e) = x ≔ e
imp2reg (c ⨟ d) = imp2reg c ⨟ imp2reg d
imp2reg (if b then c else d) = (b ?? ⨟ imp2reg c) or ((¬ b) ?? ⨟ imp2reg d)
imp2reg (while b do: c) = (b ?? ⨟ imp2reg c) * ⨟ (¬ b) ??
```

Correctness:

```
imp2reg-lemma-1 : ∀ {c} →
  c , s ⇒ s′ →
  --------------------
  imp2reg c , s ⇝*  s′

imp2reg-lemma-1 ⇒-skip = ε #

imp2reg-lemma-1 ⇒-assign = assign #

imp2reg-lemma-1 (⇒-seq c,s⇒s′′ d,s′′⇒s′)
  with imp2reg-lemma-1 c,s⇒s′′ |
       imp2reg-lemma-1 d,s′′⇒s′
... | δ₀ | δ₁ = seq-lemma δ₀ δ₁

imp2reg-lemma-1 (⇒-if-tt ⟦b⟧s≡tt c,s⇒s′) =
  or-left ,,
  seq-0 (test ⟦b⟧s≡tt) ,,
  imp2reg-lemma-1 c,s⇒s′

imp2reg-lemma-1 (⇒-if-ff {b = b} {s = s} ⟦b⟧s≡ff c,s⇒s′) =
  or-right ,,
  seq-0 (test ¬𝔹⟦b⟧s≡tt) ,,
  imp2reg-lemma-1 c,s⇒s′

  where

  ¬𝔹⟦b⟧s≡tt : ¬𝔹 B⟦ b ⟧ s ≡ tt
  ¬𝔹⟦b⟧s≡tt rewrite ⟦b⟧s≡ff = refl

imp2reg-lemma-1 (⇒-while-tt {b = b} {s = s} ⟦b⟧s≡tt c,s⇒s′ w,s′⇒s″)
  with imp2reg-lemma-1 c,s⇒s′ |
       imp2reg-lemma-1 w,s′⇒s″
... | δ₀ | δ₁ =
  seq-1 star-step ,,
  seq-1 (seq-1 (seq-0 (test ⟦b⟧s≡tt))) ,,
  assoc-seq (seq-lemma δ₀ δ₁)

imp2reg-lemma-1 (⇒-while-ff {b = b} {s = s} ⟦b⟧s≡ff) = seq-0 star-stop ,, test ¬𝔹⟦b⟧s≡tt #

  where

  ¬𝔹⟦b⟧s≡tt : ¬𝔹 B⟦ b ⟧ s ≡ tt
  ¬𝔹⟦b⟧s≡tt rewrite ⟦b⟧s≡ff = refl

-- imp2reg-lemma-2′ : ∀ {c} →
--   imp2reg c , s ⇝  s′ →
--   ---------------------
--   c , s ↝  s′

imp2reg-lemma-2 : ∀ {c} →
  imp2reg c , s ⇝* s′ →
  ---------------------
  c , s ⇒ s′

imp2reg-lemma-2 δ = {!   !}

imp2reg-lemma : ∀ {c} → c , s ⇒ s′ ↔ imp2reg c , s ⇝* s′
imp2reg-lemma = imp2reg-lemma-1 , imp2reg-lemma-2
```