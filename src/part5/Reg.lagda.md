---
title: "Regular programs 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Reg where
open import part5.Exp hiding (_↝_; _,_⇒_; ⇒-det; ↝*-trans; _↝*⟨⟩_; _↝⟨_⟩_; _↝*⟨_⟩_; _,_↝_,_; _*)
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
```

Small-steps operational semantics:

```
State = VarName → ℕ

private
  variable
    x : VarName
    e : AExp
    b : BExp
    s s′ : State
    c c′ d : Reg

infix 10 _,_⇝_
data _,_⇝_ : Reg → State → Reg × State ⊎ State → Set where

  ε : ---------------
      ε , s ⇝ right s

  assign : --------------------------------------
           x ≔ e , s ⇝ right (s [ x ↦ A⟦ e ⟧ s ])

  test : B⟦ b ⟧ s ≡ tt →
         ------------------
         b ?? , s ⇝ right s

  seq-0 : c , s ⇝ left (c′ , s′) →
          -----------------------------
          c ⨟ d , s ⇝ left (c′ ⨟ d , s′)

  seq-1 : c , s ⇝ right s′ →
          -------------------------
          c ⨟ d , s ⇝ left (d , s′)

  or-left : -------------------------
            c or d , s ⇝ left (c , s)

  or-right : -------------------------
             c or d , s ⇝ left (d , s)

  star-stop : -----------------
              c * , s ⇝ right s

  star-step : ----------------------------
              c * , s ⇝ left (c ⨟ c * , s)
```