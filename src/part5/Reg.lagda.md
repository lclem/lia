---
title: "Regular programs 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Reg where
open import part0.index hiding (AExp; A⟦_⟧; _*)
open import part5.Exp using (VarName; AExp; BExp; ¬_; B⟦_⟧_; A⟦_⟧_; _+ℕ_)
open import part5.Imp hiding (⇒-det; ↝*-trans; _↝*⟨⟩_; _↝⟨_⟩_; _↝*⟨_⟩_; ⨟-lemma-2; ⨟-lemma-1)
```

```
data Reg : Set where
  𝕠 : Reg
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
    m n k : ℕ
    x : VarName
    e : AExp
    b : BExp
    s s′ s″ : State
    c c′ c″ d : Reg

infix 10 _,_⇝_
data _,_⇝_ : Reg → State → Reg × State ⊎ State → Set where

  -- notice there is no rule for 𝕠!

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

⨟-lemma-1 : c , s ⇝* s′ →
            d , s′ ⇝* s″ →
            ---------------
            c ⨟ d , s ⇝* s″

⨟-lemma-1 (δ #) δ₁ = (seq-0 δ) ,, δ₁
⨟-lemma-1 (δ ,, δ₀) δ₁ = (seq-1 δ) ,, (⨟-lemma-1 δ₀ δ₁)

⨟-lemma-2 :
  c ⨟ d , s ⇝* s′ →
  ----------------------------------
  ∃[ s″ ] c , s ⇝* s″ × d , s″ ⇝* s′

⨟-lemma-2 (seq-0 δ₀ ,, δ₁) = _ , δ₀ # , δ₁
⨟-lemma-2 (seq-1 δ₀ ,, δ₁)
    with ⨟-lemma-2 δ₁
... | _ , δ₂ , δ₃ = _ , (δ₀ ,, δ₂) , δ₃

assoc-seq : c ⨟ (c′ ⨟ c″) , s ⇝* s′ →
            -------------------------
            (c ⨟ c′) ⨟ c″ , s ⇝* s′

assoc-seq δ
  with ⨟-lemma-2 δ
... | s″ , δ₀ , δ₁
  with ⨟-lemma-2 δ₁
... | s⁗ , δ₂ , δ₃ = ⨟-lemma-1 (⨟-lemma-1 δ₀ δ₂) δ₃
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
... | δ₀ | δ₁ = ⨟-lemma-1 δ₀ δ₁

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
  assoc-seq (⨟-lemma-1 δ₀ δ₁)

imp2reg-lemma-1 (⇒-while-ff {b = b} {s = s} ⟦b⟧s≡ff) = seq-0 star-stop ,, test ¬𝔹⟦b⟧s≡tt #

  where

  ¬𝔹⟦b⟧s≡tt : ¬𝔹 B⟦ b ⟧ s ≡ tt
  ¬𝔹⟦b⟧s≡tt rewrite ⟦b⟧s≡ff = refl

-- infix 3 _,_⇝**_,_
-- data _,_⇝**_,_ : Reg → State → Reg → State → Set where

--   stop : c , s ⇝ right s′ →
--          ------------------
--          c , s ⇝** c , s′

--   step : c , s ⇝ left (c′ , s′) →
--          c′ , s′ ⇝** c″ , s″ →
--          ------------------------
--          c , s ⇝** c″ , s″

-- imp2reg-lemma-2′ : ∀ {c c′} →
--   imp2reg c , s ⇝** imp2reg c′ , s′ →
--   -----------------------------------
--   c , s ↝ c′ , s′

-- imp2reg-lemma-2′ = {!   !}

infix 3 _,_⇝*_#_
data _,_⇝*_#_ : Reg → State → State → ℕ → Set where

  stop : c , s ⇝ right s′ →
         ------------------
         c , s ⇝* s′ # 0

  step : c , s ⇝ left (c′ , s′) →
         c′ , s′ ⇝* s″ # n →
         ------------------------
         c , s ⇝* s″ # suc n

pattern _# δ = stop δ
pattern _,,_ δ₀ δ₁ = step δ₀ δ₁

-- remove-gas : c , s ⇝* s′ # n → c , s ⇝* s′
-- remove-gas δ = {!   !}

add-gas : c , s ⇝* s′ → ∃[ n ] c , s ⇝* s′ # n
add-gas (δ #) = _ , δ #
add-gas (δ ,, δ′)
  with add-gas δ′
... | _ , δ″ = _ , (δ ,, δ″)
```

Quantitative transitivity:

```
⨟-lemma#-1 :
  c , s ⇝* s″ # m →
  d , s″ ⇝* s′ # n →
  -----------------------------
  c ⨟ d , s ⇝* s′ # suc (m + n)

⨟-lemma#-1 (δ₀ #) δ₁ = seq-0 δ₀ ,, δ₁
⨟-lemma#-1 (δ ,, δ₀) δ₁
  with ⨟-lemma#-1 δ₀ δ₁
... | δ₂ = seq-1 δ ,, δ₂
```

The following lemma is analogous to !remoteRef(part5)(Imp)(⨟-lemma-2)

```
⨟-lemma#-2 :
  c ⨟ d , s ⇝* s′ # m →
  -------------------------
  ∃[ s″ ] ∃[ m1 ] ∃[ m2 ]
      c , s ⇝* s″ # m1 ×
      d , s″ ⇝* s′ # m2 ×
      suc (m1 +ℕ m2) ≡ m

⨟-lemma#-2 (seq-0 δ₀ ,, δ) = _ , 0 , _ , δ₀ # , δ , refl

⨟-lemma#-2 (seq-1 δ₀ ,, δ)
  with ⨟-lemma#-2 δ
... | s″ , m₁ , m₂ , δ₁ , δ₂ , m1+m2≡n =
      s″ , suc m₁ , m₂ , (δ₀ ,, δ₁) , δ₂ , cong suc m1+m2≡n
```

```
imp2reg-lemma-2 : ∀ c →
  imp2reg c , s ⇝* s′ # n →
  -------------------------
  c , s ⇒ s′

-- imp2reg-lemma-2 skip (ε #) = ⇒-skip
-- imp2reg-lemma-2 (x ≔ e) (assign #) = ⇒-assign
-- imp2reg-lemma-2 (c ⨟ d) δ = {!   !}
-- imp2reg-lemma-2 (if x then c else c₁) δ = {!   !}
-- imp2reg-lemma-2 (while x do: c) δ = {!   !}

imp2reg-lemma-2 {n = n} c δ = go c δ (<-wf n) where

  go : ∀ c {n} →
    imp2reg c , s ⇝* s′ # n →
    Acc _<_ n →
    -------------------------
    c , s ⇒ s′

  go skip (ε #) (acc a) = ⇒-skip

  go (x ≔ e) (assign #) (acc a) = ⇒-assign

  go (c ⨟ d) δ (acc a)
    with ⨟-lemma#-2 δ
  ... | s‶ , m₁ , m₂ , δ₁ , δ₂ , eq rewrite sym eq
    with go c δ₁ (a m₁ (s≤s mon-≤-left)) |
         go d δ₂ (a m₂ (s≤s mon-≤-right))
  ... | ⇒-der1 | ⇒-der2 = ⇒-seq ⇒-der1 ⇒-der2

  go (if b then c else _) (or-left ,, seq-0 (test ⟦b⟧s≡tt) ,, δ) (acc a)
    with go c δ (a _ n<suc2n)
  ... | ⇒-der = ⇒-if-tt ⟦b⟧s≡tt ⇒-der

  go (if b then _ else d) (or-right ,, seq-0 (test ⟦¬b⟧s≡tt) ,, δ) (acc a)
    with go d δ (a _ n<suc2n)
  ... | ⇒-der = ⇒-if-ff (¬𝔹-tt-ff ⟦¬b⟧s≡tt) ⇒-der where

  go (while b do: c) (seq-0 star-stop ,, test ⟦¬b⟧s≡tt #) (acc a) = ⇒-while-ff (¬𝔹-tt-ff ⟦¬b⟧s≡tt)
  
  go (while b do: c) (seq-1 star-step ,, seq-1 (seq-1 (seq-0 (test ⟦b⟧s≡tt))) ,, δ) (acc a)
    with ⨟-lemma#-2 δ 
  ... | s‶ , m₁ , m₂ , δ₁ , δ₂ , eq
    with ⨟-lemma#-2 δ₁
  ... | s‷  , m₃ , m₄ , δ₃ , δ₄ , eq′
    rewrite sym eq | sym eq′ | assoc-+ {m₃} {m₄} {m₂}
    with go c δ₃ (a _ (s≤s (mon-trans-≤-right {n = 3} mon-≤-left))) |
         go _ (⨟-lemma#-1 δ₄ δ₂) (a _ (s≤s (s≤s (mon-trans-≤-right {n = 2} (mon-≤-right {m₄ +ℕ m₂} {m₃})))))
  ... | ⇒-der1 | ⇒-der2 = ⇒-while-tt ⟦b⟧s≡tt ⇒-der1 ⇒-der2

imp2reg-lemma : ∀ {c} → c , s ⇒ s′ ↔ imp2reg c , s ⇝* s′
imp2reg-lemma = imp2reg-lemma-1 , λ δ → let _ , δ′ = add-gas δ in imp2reg-lemma-2 _ δ′
```

Notice that neither direction of the simulation is sufficient alone.
For instance, if we only required the "only if" direction,
then we could define `imp2reg c` to be any regular program that nondeterministically can reach an arbitrary state.
And if we only required the "if" direction,
then we could define `imp2reg c` to be a regular program that does not reach any state at all (such as !ref(Reg)(𝕠) or `ff ??`).