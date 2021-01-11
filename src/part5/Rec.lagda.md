---
title: "First-order recursion 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Rec where
open import part0.index hiding (AExp; A⟦_⟧; _≈_; _⊑_; _$_; trans-⊑; refl-⊑) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _∸_ to _-ℕ_; _≤_ to _≤ℕ_) public
```

Syntax:

```
VarName = ℕ
FunName = ℕ

x₀ x₁ : VarName
x₀ = 0
x₁ = 1

f₀ f₁ : FunName
f₀ = 0
f₁ = 1

data Exp : Set where
  #_ : (n : ℕ) → Exp
  `_ : (x : VarName) → Exp
  _+_ _-_ _·_ : (e₀ e₁ : Exp) → Exp
  If_Then_Else_ : (e₀ e₁ e₂ : Exp) → Exp
  _$_ : (f : FunName) (e : Exp) → Exp
  Let_≔_In_ : (x : VarName) (e f : Exp) → Exp
  Rec_[_]≔_In_ : (f : FunName) (x : VarName) (e₀ e₁ : Exp) → Exp

private
  variable
    x y : VarName
    f : FunName
    e e′ e₀ e₁ e₂ : Exp
    k k′ k₀ k₁ m n n₀ n₁ : ℕ
```

```
infix 50 #_ `_
infixl 25 _+_ _-_
infixl 26 _·_
infixl 30 _$_
infixr 20 If_Then_Else_
infixr 15 Let_≔_In_ Rec_[_]≔_In_
```

Example:

```
factorial : Exp
factorial = Rec f₀ [ x₀ ]≔ If (` x₀) Then (# 1) Else ((` x₀) · f₀ $ (` x₀ - # 1)) In f₀ $ # 5
```

# Eager evaluation with dynamic binding

Eager semantics means that when evaluating an application (call) `f $ e` we must evaluate the argument `e` before passing it to `f`.
The same applies to `Let x ≔ e₀ In e₁`.

Dynamic binding means that the free numerical and functional variables appearing in `e₀` in `Rec f [ x ]≔ e₀ In e₁` are evaluated according to the environment at the time of call.
The same applies to `Let x ≔ e₀ In e₁`.

```
VarEnv = VarName → ℕ
FunEnv = FunName → (VarName × Exp)

Env = VarEnv × FunEnv

ϱ₀ : VarEnv
ϱ₀ = const 0

-- τ₀ : FunEnv
-- τ₀ = const (x₀ , # 0)

-- γ₀ : Env
-- γ₀ = ϱ₀ , τ₀

private
  variable
    γ γ₀ γ₁ : Env
    ϱ : VarEnv
    τ τ′ τ₀ τ₁ : FunEnv
```

## Natural semantics

```
infix 4 _,_⇒_
data _,_⇒_ : Exp → Env → ℕ → Set where

  instance
    ⇒-Num :
      ------------
      # n , γ ⇒ n

  instance 
    ⇒-Var :
      --------------------
      ` x , (ϱ , τ) ⇒ ϱ x

  ⇒-Add :
    e₀ , γ ⇒ n₀ →
    e₁ , γ ⇒ n₁ →
    ------------------
    e₀ + e₁ , γ ⇒ n₀ +ℕ n₁

  ⇒-Sub :
    e₀ , γ ⇒ n₀ →
    e₁ , γ ⇒ n₁ →
    ------------------
    e₀ - e₁ , γ ⇒ n₀ -ℕ n₁

  ⇒-Mul :
    e₀ , γ ⇒ n₀ →
    e₁ , γ ⇒ n₁ →
    ------------------
    e₀ · e₁ , γ ⇒ n₀ ·ℕ n₁

  ⇒-IfThenElse-tt :
    e₀ , γ ⇒ 0 →
    e₁ , γ ⇒ n →
    -----------------------------
    If e₀ Then e₁ Else e₂ , γ ⇒ n

  ⇒-IfThenElse-ff :
    e₀ , γ ⇒ suc m →
    e₂ , γ ⇒ n →
    -----------------------------
    If e₀ Then e₁ Else e₂ , γ ⇒ n

  ⇒-App :
    e , (ϱ , τ) ⇒ m →
    let (x , e′) = τ f in
    e′ , (ϱ [ x ↦ m ] , τ) ⇒ n →
    -----------------------------
    (f $ e) , (ϱ , τ) ⇒ n

  ⇒-Let :
    e₀ , (ϱ , τ) ⇒ m →
    e₁ , (ϱ [ x ↦ m ] , τ) ⇒ n →
    -------------------------------
    Let x ≔ e₀ In e₁ , (ϱ , τ) ⇒ n

  ⇒-Rec :
    e₁ , (ϱ , τ [ f ↦ x , e₀ ]) ⇒ n →
    ------------------------------------
    Rec f [ x ]≔ e₀ In e₁ , (ϱ , τ) ⇒ n
```

```
instance instance-Add : ⦃ e₀ , γ ⇒ n₀ ⦄ → ⦃ e₁ , γ ⇒ n₁ ⦄ → e₀ + e₁ , γ ⇒ n₀ +ℕ n₁
instance-Add = ⇒-Add by-inst by-inst

instance instance-Sub : ⦃ e₀ , γ ⇒ n₀ ⦄ → ⦃ e₁ , γ ⇒ n₁ ⦄ → e₀ - e₁ , γ ⇒ n₀ -ℕ n₁
instance-Sub = ⇒-Sub by-inst by-inst

instance instance-Mul : ⦃ e₀ , γ ⇒ n₀ ⦄ → ⦃ e₁ , γ ⇒ n₁ ⦄ → e₀ · e₁ , γ ⇒ n₀ ·ℕ n₁
instance-Mul = ⇒-Mul by-inst by-inst

-- instance instance-Add : ⦃ e₀ , γ ⇒ n₀ ⦄ → ⦃ e₁ , γ ⇒ n₁ ⦄ → e₀ + e₁ , γ ⇒ n₀ +ℕ n₁
-- instance-Add = ⇒-Add by-inst by-inst

-- instance instance-Add : ⦃ e₀ , γ ⇒ n₀ ⦄ → ⦃ e₁ , γ ⇒ n₁ ⦄ → e₀ + e₁ , γ ⇒ n₀ +ℕ n₁
-- instance-Add = ⇒-Add by-inst by-inst

-- instance instance-Add : ⦃ e₀ , γ ⇒ n₀ ⦄ → ⦃ e₁ , γ ⇒ n₁ ⦄ → e₀ + e₁ , γ ⇒ n₀ +ℕ n₁
-- instance-Add = ⇒-Add by-inst by-inst

-- instance instance-Add : ⦃ e₀ , γ ⇒ n₀ ⦄ → ⦃ e₁ , γ ⇒ n₁ ⦄ → e₀ + e₁ , γ ⇒ n₀ +ℕ n₁
-- instance-Add = ⇒-Add by-inst by-inst

-- instance instance-Add : ⦃ e₀ , γ ⇒ n₀ ⦄ → ⦃ e₁ , γ ⇒ n₁ ⦄ → e₀ + e₁ , γ ⇒ n₀ +ℕ n₁
-- instance-Add = ⇒-Add by-inst by-inst

instance instance-Rec : ⦃ e₁ , (ϱ , τ [ f ↦ x , e₀ ]) ⇒ n ⦄ → Rec f [ x ]≔ e₀ In e₁ , (ϱ , τ) ⇒ n
instance-Rec ⦃ δ ⦄ = ⇒-Rec δ
```

Example:

```
_ : # 4 + # 3 , γ₀ ⇒ 7
_ = by-inst
```

## Denotational semantics

Evaluation with gas:

```
data ℕ⊥ : Set where
  ⊥ : ℕ⊥
  ⌊_⌋ : ℕ → ℕ⊥

infix 10 ⌊_⌋

private variable m⊥ n⊥ u v u₀ u₁ u₂ v₀ v₁ v₂ : ℕ⊥

Just-inv : ⌊ m ⌋ ≡ ⌊ n ⌋ → m ≡ n
Just-inv refl = refl

⊥≡Just-elim : ⊥ ≡ ⌊ m ⌋ → ∀ {ℓ} {A : Set ℓ} → A
⊥≡Just-elim ()

infix 5 _⊑_ _⊒_
data _⊑_ : ℕ⊥ → ℕ⊥ → Set where
  ⊑-⊥ : ⊥ ⊑ m⊥
  ⊑-Just : ⌊ m ⌋ ⊑ ⌊ m ⌋

refl-⊑ : v ⊑ v
refl-⊑ {⊥} = ⊑-⊥
refl-⊑ {⌊ _ ⌋} = ⊑-Just

trans-⊑ : v₀ ⊑ v₁ → v₁ ⊑ v₂ → v₀ ⊑ v₂
trans-⊑ ⊑-⊥ ⊑-Just = ⊑-⊥
trans-⊑ ⊑-⊥ ⊑-⊥ = ⊑-⊥
trans-⊑ ⊑-Just ⊑-Just = ⊑-Just

_⊒_ : ℕ⊥ → ℕ⊥ → Set
v₀ ⊒ v₁ = v₁ ⊑ v₀ 

⊑-⊥-lemma : v ⊑ ⊥ → v ≡ ⊥
⊑-⊥-lemma ⊑-⊥ = refl

⊑-Just-lemma : ⌊ m ⌋ ⊑ n⊥ → n⊥ ≡ ⌊ m ⌋
⊑-Just-lemma ⊑-Just = refl

lift : (ℕ → ℕ) → ℕ⊥ → ℕ⊥
lift f ⊥ = ⊥
lift f (⌊ x ⌋) = ⌊ f x ⌋

lift2 : (ℕ → ℕ → ℕ) → ℕ⊥ → ℕ⊥ → ℕ⊥
lift2 f ⊥ _ = ⊥
lift2 f (⌊ _ ⌋) ⊥ = ⊥
lift2 f (⌊ m ⌋) (⌊ n ⌋) = ⌊ f m n ⌋

lift2-lemma : ∀ f →
  lift2 f v₀ v₁ ≡ ⌊ n ⌋ →
  -------------------------------------------
  ∃[ n₀ ] ∃[ n₁ ] v₀ ≡ ⌊ n₀ ⌋ × v₁ ≡ ⌊ n₁ ⌋

lift2-lemma {v₀} {v₁} f eq
  with v₀ | v₁
... | ⌊ n₀ ⌋ | ⌊ n₁ ⌋ = n₀ , n₁ , refl , refl

mon-lift2 : (f : ℕ → ℕ → ℕ) →
  u₀ ⊑ u₁ →
  v₀ ⊑ v₁ →
  -----------------------------
  lift2 f u₀ v₀ ⊑ lift2 f u₁ v₁
  
mon-lift2 f ⊑-⊥ ⊑-⊥ = ⊑-⊥
mon-lift2 f ⊑-⊥ ⊑-Just = ⊑-⊥
mon-lift2 f ⊑-Just ⊑-⊥ = ⊑-⊥
mon-lift2 f ⊑-Just ⊑-Just = ⊑-Just

infixl 13 _+⊥_ _-⊥_
infixl 14 _·⊥_

_+⊥_ _-⊥_ _·⊥_ : ℕ⊥ → ℕ⊥ → ℕ⊥
_+⊥_ = lift2 _+ℕ_
_-⊥_ = lift2 _-ℕ_
_·⊥_ = lift2 _·ℕ_

ite : ℕ⊥ → ℕ⊥ → ℕ⊥ → ℕ⊥
ite ⊥ _ _ = ⊥
ite (⌊ 0 ⌋) v₀ v₁ = v₀
ite (⌊ suc _ ⌋) v₀ v₁ = v₁

mon-ite : u₀ ⊑ v₀ → u₁ ⊑ v₁ → u₂ ⊑ v₂ → ite u₀ u₁ u₂ ⊑ ite v₀ v₁ v₂
mon-ite ⊑-⊥ _ _ = ⊑-⊥
mon-ite {u₀ = ⌊ 0 ⌋} ⊑-Just u₁⊑v₁ u₂⊑v₂ = u₁⊑v₁
mon-ite {u₀ = ⌊ suc _ ⌋} ⊑-Just u₁⊑v₁ u₂⊑v₂ = u₂⊑v₂

⟦_⟧_#_ : Exp → Env → ℕ → ℕ⊥

⟦ _ ⟧ _ # 0 = ⊥

⟦ # n ⟧ γ # suc _ = ⌊ n ⌋
⟦ ` x ⟧ (ϱ , _) # suc _ = ⌊ ϱ x ⌋

⟦ e₀ + e₁ ⟧ γ # suc k = ⟦ e₀ ⟧ γ # k +⊥ ⟦ e₁ ⟧ γ # k
⟦ e₀ - e₁ ⟧ γ # suc k = ⟦ e₀ ⟧ γ # k -⊥ ⟦ e₁ ⟧ γ # k
⟦ e₀ · e₁ ⟧ γ # suc k = ⟦ e₀ ⟧ γ # k ·⊥ ⟦ e₁ ⟧ γ # k

⟦ If e₀ Then e₁ Else e₂ ⟧ γ # suc k = ite (⟦ e₀ ⟧ γ # k) (⟦ e₁ ⟧ γ # k) (⟦ e₂ ⟧ γ # k)

⟦ f $ e ⟧ γ@(ϱ , τ) # suc k
  with ⟦ e ⟧ γ # k
... | ⊥ = ⊥
... | ⌊ m ⌋ = let x , e′ = τ f in ⟦ e′ ⟧ (ϱ [ x ↦ m ] , τ) # k

⟦ Let x ≔ e₀ In e₁ ⟧ γ@(ϱ , τ) # suc k
  with ⟦ e₀ ⟧ γ # k
... | ⊥ = ⊥
... | ⌊ m ⌋ = ⟦ e₁ ⟧ (ϱ [ x ↦ m ] , τ) # k

⟦ Rec f [ x ]≔ e₀ In e₁ ⟧ (ϱ , τ) # suc k = ⟦ e₁ ⟧ (ϱ , τ [ f ↦ x , e₀ ]) # k
```

```
_ : ⟦ If # 0 Then # 20 · # 30 - # 1 Else # 20 ⟧ γ₀ # 10 ≡ ⌊ 599 ⌋
_ = refl

_ : ⟦ factorial ⟧ γ₀ # 1000 ≡ ⌊ 120 ⌋
_ = refl
```

Denotational convergence to a value:

```
⟦_⟧_⇓_ : Exp → Env → ℕ → Set
⟦ e ⟧ γ ⇓ n = ∃[ k ] ⟦ e ⟧ γ # k ≡ ⌊ n ⌋
```

Monotonicity of evaluation w.r.t. the number of steps
(more steps → more values):

```
mon-eval : ∀ e →
           ⟦ e ⟧ γ # k ⊒ v →
           k ≤ℕ k′ →
           ------------------
           ⟦ e ⟧ γ # k′ ⊒ v

mon-eval {k = zero} _ ⊑-⊥ k≤k′ = ⊑-⊥

mon-eval {k = suc k} {k′ = suc k′} (# n) ⟦e⟧⊒v (s≤s k≤k′) = ⟦e⟧⊒v
mon-eval {k = suc k} {k′ = suc k′} (` x) ⟦e⟧⊒v (s≤s k≤k′) = ⟦e⟧⊒v

mon-eval {k = suc k} {k′ = suc k′} (e₀ + e₁) ⟦e⟧⊒v (s≤s k≤k′)
  with mon-eval e₀ refl-⊑ k≤k′ |
       mon-eval e₁ refl-⊑ k≤k′
... | ind₀ | ind₁ = trans-⊑ ⟦e⟧⊒v (mon-lift2 _+ℕ_ ind₀ ind₁)

mon-eval {k = suc k} {k′ = suc k′} (e₀ - e₁) ⟦e⟧⊒v (s≤s k≤k′)
  with mon-eval e₀ refl-⊑ k≤k′ |
       mon-eval e₁ refl-⊑ k≤k′
... | ind₀ | ind₁ = trans-⊑ ⟦e⟧⊒v (mon-lift2 _-ℕ_ ind₀ ind₁)

mon-eval {k = suc k} {k′ = suc k′} (e₀ · e₁) ⟦e⟧⊒v (s≤s k≤k′)
  with mon-eval e₀ refl-⊑ k≤k′ |
       mon-eval e₁ refl-⊑ k≤k′
... | ind₀ | ind₁ = trans-⊑ ⟦e⟧⊒v (mon-lift2 _·ℕ_ ind₀ ind₁)

mon-eval {k = suc k} {k′ = suc k′} (If e₀ Then e₁ Else e₂) ⟦e⟧⊒v (s≤s k≤k′)
  with mon-eval e₀ refl-⊑ k≤k′ |
       mon-eval e₁ refl-⊑ k≤k′ |
       mon-eval e₂ refl-⊑ k≤k′
... | ind₀ | ind₁ | ind₂ = trans-⊑ ⟦e⟧⊒v (mon-ite ind₀ ind₁ ind₂)

mon-eval {γ@(ϱ , τ)} {suc k} {v} {suc k′} (f $ e) ⟦e⟧⊒v (s≤s k≤k′)
  with inspect (⟦ e ⟧ γ # k)
... | it ⊥ eq-e rewrite eq-e | ⊑-⊥-lemma ⟦e⟧⊒v = ⊑-⊥
... | it (⌊ m ⌋) eq-e
  with inspect (τ f) |
       mon-eval {γ = γ} e refl-⊑ k≤k′
... | it (x , e′) eq-τ | ind-e
  rewrite eq-e | ⊑-Just-lemma ind-e | eq-τ
  with mon-eval {γ = ϱ [ x ↦ m ] , τ} e′ refl-⊑ k≤k′
... | ind-e′ = trans-⊑ ⟦e⟧⊒v ind-e′

mon-eval {γ@(ϱ , τ)} {suc k} {v} {suc k′} (Let x ≔ e₀ In e₁) ⟦e⟧⊒v (s≤s k≤k′)
  with inspect (⟦ e₀ ⟧ γ # k)
... | it ⊥ eq-e₀
  rewrite eq-e₀ | ⊑-⊥-lemma ⟦e⟧⊒v = ⊑-⊥
... | it (⌊ m ⌋) eq-e₀
  with mon-eval {γ = γ} e₀ refl-⊑ k≤k′
... | ind-e₀
  rewrite eq-e₀ | ⊑-Just-lemma ind-e₀
    with mon-eval {γ = ϱ [ x ↦ m ] , τ} e₁ refl-⊑ k≤k′
... | ind-e₁ = trans-⊑ ⟦e⟧⊒v ind-e₁

mon-eval {γ@(ϱ , τ)} {suc k} {v} {suc k′} (Rec f [ x ]≔ e₀ In e₁) ⟦e⟧⊒v (s≤s k≤k′)
  with mon-eval {γ = ϱ , τ [ f ↦ x , e₀ ]} e₁ refl-⊑ k≤k′
... | ind-e₁ = trans-⊑ ⟦e⟧⊒v ind-e₁
```

## Agreement of the semantics

```
agree-1 : ∀ e k →
  ⟦ e ⟧ γ # k ≡ ⌊ n ⌋ →
  ----------------------
  e , γ ⇒ n

agree-1 (# n) (suc k) refl = ⇒-Num

agree-1 (` x) (suc k) refl = ⇒-Var

agree-1 (e₀ + e₁) (suc k) eq
  with lift2-lemma _+ℕ_ eq
... | n₀ , n₁ , eq₀ , eq₁
  with agree-1 e₀ k eq₀ |
       agree-1 e₁ k eq₁
... | ind₀ | ind₁
  rewrite eq₀ | eq₁ | sym (Just-inv eq) = ⇒-Add ind₀ ind₁

agree-1 (e₀ - e₁) (suc k) eq
  with lift2-lemma _-ℕ_ eq
... | n₀ , n₁ , eq₀ , eq₁
  with agree-1 e₀ k eq₀ |
       agree-1 e₁ k eq₁
... | ind₀ | ind₁ rewrite eq₀ | eq₁ | sym (Just-inv eq) = ⇒-Sub ind₀ ind₁

agree-1 (e₀ · e₁) (suc k) eq
  with lift2-lemma _·ℕ_ eq
... | n₀ , n₁ , eq₀ , eq₁
  with agree-1 e₀ k eq₀ |
       agree-1 e₁ k eq₁
... | ind₀ | ind₁ rewrite eq₀ | eq₁ | sym (Just-inv eq) = ⇒-Mul ind₀ ind₁

agree-1 {γ} (If e₀ Then e₁ Else e₂) (suc k) eq
  with inspect (⟦ e₀ ⟧ γ # k)
... | it ⊥ eq-e₀ rewrite eq-e₀ = ⊥≡Just-elim eq
... | it (⌊ 0 ⌋) eq-e₀ rewrite eq-e₀ = ⇒-IfThenElse-tt (agree-1 e₀ k eq-e₀) (agree-1 e₁ k eq)
... | it (⌊ suc _ ⌋) eq-e₀ rewrite eq-e₀ = ⇒-IfThenElse-ff (agree-1 e₀ k eq-e₀) (agree-1 e₂ k eq)

agree-1 {γ@(ϱ , τ)} {n} (f $ e) (suc k) eq
  with inspect (⟦ e ⟧ γ # k)
... | it ⊥ eq-e rewrite eq-e = ⊥≡Just-elim eq
... | it (⌊ m ⌋) eq-e
  with inspect (τ f) |
       agree-1 {γ} e k eq-e
... | it (x , e′) eq-τ | ind-e
  rewrite eq-e | eq-τ
  with agree-1 {ϱ [ x ↦ m ] , τ} e′ k eq
... | ind-e′ = ⇒-App ind-e goal where

    goal : snd (τ f) , (ϱ [ fst (τ f) ↦ m ] , τ) ⇒ n
    goal rewrite eq-τ = ind-e′

agree-1 {γ} (Let x ≔ e₀ In e₁) (suc k) eq
  with inspect (⟦ e₀ ⟧ γ # k)
... | it ⊥ eq-e₀ rewrite eq-e₀ = ⊥≡Just-elim eq
... | it (⌊ m ⌋) eq-e₀
  rewrite eq-e₀
  with agree-1 e₀ k eq-e₀ |
       agree-1 e₁ k eq
... | ind-e₀ | ind-e₁ = ⇒-Let ind-e₀ ind-e₁

agree-1 {γ@(ϱ , τ)} (Rec f [ x ]≔ e₀ In e₁) (suc k) eq
  with agree-1 {γ = ϱ , τ [ f ↦ x , e₀ ]} e₁ k eq
... | ind-e₀ = ⇒-Rec ind-e₀
```

```
help : ∀ k₀ k₁ →
       ⟦ e₀ ⟧ γ₀ # k₀ ≡ ⌊ n₀ ⌋ →
       ⟦ e₁ ⟧ γ₁ # k₁ ≡ ⌊ n₁ ⌋ →
       ---------------------------------
       ⟦ e₀ ⟧ γ₀ # max k₀ k₁ ≡ ⌊ n₀ ⌋ ×
       ⟦ e₁ ⟧ γ₁ # max k₀ k₁ ≡ ⌊ n₁ ⌋

help {e₀} {γ₀} {n₀} {e₁} {γ₁} {n₁} k₀ k₁ eq₀ eq₁
  with max-left {k₀} {k₁} |
       max-right {k₁} {k₀}
... | k₀≤max | k₁≤max
  with mon-eval {γ₀} e₀ refl-⊑ k₀≤max |
       mon-eval {γ₁} e₁ refl-⊑ k₁≤max
... | le₀ | le₁
  rewrite eq₀ | eq₁ = ⊑-Just-lemma le₀ , ⊑-Just-lemma le₁

help2 : ∀ f → u ≡ ⌊ m ⌋ → v ≡ ⌊ n ⌋ → lift2 f u v ≡ ⌊ f m n ⌋
help2 _ refl refl = refl

agree-2 : e , γ ⇒ n →
          -----------
          ⟦ e ⟧ γ ⇓ n

agree-2-help :
  e₀ , γ ⇒ n₀ →
  e₁ , γ ⇒ n₁ →
  ---------------------------------
  ∃[ k₀ ] ∃[ k₁ ]
    ⟦ e₀ ⟧ γ # max k₀ k₁ ≡ ⌊ n₀ ⌋ ×
    ⟦ e₁ ⟧ γ # max k₀ k₁ ≡ ⌊ n₁ ⌋

agree-2-help δ₀ δ₁
  with agree-2 δ₀ | agree-2 δ₁
... | k₀ , eq₀ | k₁ , eq₁
  with help k₀ k₁ eq₀ eq₁
... | eq₀′ , eq₁′ = k₀ , k₁ , eq₀′ , eq₁′

agree-2 ⇒-Num = 1 , refl
agree-2 ⇒-Var = 1 , refl

agree-2 (⇒-Add δ₀ δ₁)
  with agree-2-help δ₀ δ₁
... | k₀ , k₁ , eq₀′ , eq₁′ = suc (max k₀ k₁) , help2 _+ℕ_ eq₀′ eq₁′

agree-2 (⇒-Sub δ₀ δ₁)
  with agree-2-help δ₀ δ₁
... | k₀ , k₁ , eq₀′ , eq₁′ = suc (max k₀ k₁) , help2 _-ℕ_ eq₀′ eq₁′

agree-2 (⇒-Mul δ₀ δ₁)
  with agree-2-help δ₀ δ₁
... | k₀ , k₁ , eq₀′ , eq₁′ = suc (max k₀ k₁) , help2 _·ℕ_ eq₀′ eq₁′

agree-2 {If e₀ Then e₁ Else e₂} {γ} {n} (⇒-IfThenElse-tt δ₀ δ₁)
  with agree-2-help δ₀ δ₁
... | k₀ , k₁ , eq₀′ , eq₁′ = suc (max k₀ k₁) , goal where

  goal : ite (⟦ e₀ ⟧ γ # max k₀ k₁) (⟦ e₁ ⟧ γ # max k₀ k₁) (⟦ e₂ ⟧ γ # max k₀ k₁) ≡ ⌊ n ⌋
  goal rewrite eq₀′ | eq₁′ = refl

agree-2 {If e₀ Then e₁ Else e₂} {γ} {n} (⇒-IfThenElse-ff δ₀ δ₁)
  with agree-2-help δ₀ δ₁
... | k₀ , k₁ , eq₀′ , eq₁′ = suc (max k₀ k₁) , goal where

  goal : ite (⟦ e₀ ⟧ γ # max k₀ k₁) (⟦ e₁ ⟧ γ # max k₀ k₁) (⟦ e₂ ⟧ γ # max k₀ k₁) ≡ ⌊ n ⌋
  goal rewrite eq₀′ | eq₁′ = refl

agree-2 {f $ e} {γ@(ϱ , τ)} {n} (⇒-App δ₀ δ₁)
  with inspect (τ f) | agree-2 δ₀ | agree-2 δ₁
... | it (x , e′) eq-τ | k₀ , eq₀ | k₁ , eq₁
  with help k₀ k₁ eq₀  eq₁
... | eq₀′ , eq₁′ = suc (max k₀ k₁) , goal where

  goal : ⟦ f $ e ⟧ ϱ , τ # suc (max k₀ k₁) ≡ ⌊ n ⌋
  goal rewrite eq₀′ | eq₁′ | eq-τ = refl

agree-2 e@{Let x ≔ e₀ In e₁} {γ@(ϱ , τ)} {n} (⇒-Let δ₀ δ₁)
  with agree-2 δ₀ | agree-2 δ₁
... | k₀ , eq₀ | k₁ , eq₁
  with help k₀ k₁ eq₀  eq₁
... | eq₀′ , eq₁′ = suc (max k₀ k₁) , goal where

  goal : ⟦ e ⟧ ϱ , τ # suc (max k₀ k₁) ≡ ⌊ n ⌋
  goal rewrite eq₀′ | eq₁′ = refl

agree-2 {Rec f [ x ]≔ e₀ In e₁} {γ@(ϱ , τ)} {n} (⇒-Rec δ)
  with agree-2 δ
... | k , eq = suc k , eq
```

```
agree : ∀ e → ⟦ e ⟧ γ ⇓ n ↔ e , γ ⇒ n
agree e = (λ{ (k , eq) → agree-1 e k eq }) , agree-2
```

## Contextual equivalence

Notice that we only have zeroth-order contexts in this language,
i.e., we can only replace an integral variable `x` with an expression of the language.

Substitution:

```
infix 101 _E[_↦_]
_E[_↦_] : Exp → VarName → Exp → Exp

(# n) E[ x ↦ f ] = # n

(` y) E[ x ↦ f ]
  with x ≡? y
... | yes _ = f
... | no _ = ` y

(e₀ + e₁) E[ x ↦ f ] = e₀ E[ x ↦ f ] + e₁ E[ x ↦ f ]
(e₀ - e₁) E[ x ↦ f ] = e₀ E[ x ↦ f ] - e₁ E[ x ↦ f ]
(e₀ · e₁) E[ x ↦ f ] = e₀ E[ x ↦ f ] · e₁ E[ x ↦ f ]

(If e₀ Then e₁ Else e₂) E[ x ↦ f ] = If e₀ E[ x ↦ f ] Then e₁ E[ x ↦ f ] Else e₂ E[ x ↦ f ]

(g $ e) E[ x ↦ f ] = g $ e E[ x ↦ f ]

(Let y ≔ e₀ In e₁) E[ x ↦ f ]
  with x ≡? y | e₀ E[ x ↦ f ]
... | yes _ | e′ = Let y ≔ e′ In e₁
... | no _ | e′ = Let y ≔ e′ In e₁ E[ x ↦ f ]

(Rec g [ y ]≔ e₀ In e₁) E[ x ↦ f ]
  with x ≡? y | e₁ E[ x ↦ f ]
... | yes _ | e′ = Rec g [ y ]≔ e₀ In e′
... | no _ | e′ = Rec g [ y ]≔ e₀ E[ x ↦ f ] In e′
```

Operational equivalence:

```
_∼_ : ∀ e₀ e₁ → Set
e₀ ∼ e₁ = ∀ γ n → e₀ , γ ⇒ n ↔ e₁ , γ ⇒ n

sym-∼ : e₀ ∼ e₁ → e₁ ∼ e₀
sym-∼ e₀∼e₁ γ n = snd (e₀∼e₁ γ n) , (fst (e₀∼e₁ γ n))
```

Operational simulation (one-sided version):

```
_≾_ : ∀ e₀ e₁ → Set
e₀ ≾ e₁ = ∀ γ n → e₀ , γ ⇒ n → e₁ , γ ⇒ n

∼→≾ : e₀ ∼ e₁ → e₀ ≾ e₁
∼→≾ e₀∼e₁ γ n = fst (e₀∼e₁ γ n)
```

Operational simulation is a preorder:

```
refl-≾ : e ≾ e
refl-≾ γ n = id
```

Extended to function environments:

```
_≾FunEnv_ : (τ τ′ : FunEnv) → Set
τ ≾FunEnv τ′ = ∀[ f ]
  let (x , e) = τ f 
      (x′ , e′ ) = τ′ f in
      x ≡ x′ × e ≾ e′

refl-≾FunEnv : τ ≾FunEnv τ
refl-≾FunEnv  f = refl , refl-≾

≾FunEnv-update-1 : ∀ f → e₀ ≾ e₁ → τ [ f ↦ x , e₀ ] ≾FunEnv τ [ f ↦ x , e₁ ]
≾FunEnv-update-1 {τ = τ} f e₀≾e₁ g  
  with f ≡? g
... | yes refl = refl , e₀≾e₁
... | no _ = refl-≾FunEnv {τ = τ} g

-- ≾FunEnv-update : ∀ f →
--   τ₀ ≾FunEnv τ₁ →
--   e₀ ≾ e₁ →
--   -------------------------------------------
--   τ₀ [ f ↦ x , e₀ ] ≾FunEnv τ₁ [ f ↦ x , e₁ ]

-- ≾FunEnv-update = {!   !}

≾FunEnv-update-same : ∀ f →
  τ₀ ≾FunEnv τ₁ →
  -------------------------------------------
  τ₀ [ f ↦ x , e ] ≾FunEnv τ₁ [ f ↦ x , e ]

≾FunEnv-update-same f τ₀≾τ₁ g
  with f ≡? g | τ₀≾τ₁ g
... | yes refl | eq , _ rewrite eq = refl , λ _ _ → id
... | no _ | eq , τ₀g≾τ₁g rewrite eq = refl , τ₀g≾τ₁g
```

```
mon-≾FunEnv :
  e , (ϱ , τ) ⇒ m →
  τ ≾FunEnv τ′ →
  -----------------
  e , (ϱ , τ′) ⇒ m

mon-≾FunEnv ⇒-Num τ≾τ′ = ⇒-Num
mon-≾FunEnv ⇒-Var τ≾τ′ = ⇒-Var

mon-≾FunEnv (⇒-Add δ₀ δ₁) τ≾τ′
  with mon-≾FunEnv δ₀ τ≾τ′ |
       mon-≾FunEnv δ₁ τ≾τ′
... | ind₀ | ind₁ = ⇒-Add ind₀ ind₁

mon-≾FunEnv (⇒-Sub δ₀ δ₁) τ≾τ′
  with mon-≾FunEnv δ₀ τ≾τ′ |
       mon-≾FunEnv δ₁ τ≾τ′
... | ind₀ | ind₁ = ⇒-Sub ind₀ ind₁

mon-≾FunEnv (⇒-Mul δ₀ δ₁) τ≾τ′
  with mon-≾FunEnv δ₀ τ≾τ′ |
       mon-≾FunEnv δ₁ τ≾τ′
... | ind₀ | ind₁ = ⇒-Mul ind₀ ind₁

mon-≾FunEnv (⇒-IfThenElse-tt δ₀ δ₁) τ≾τ′
  with mon-≾FunEnv δ₀ τ≾τ′ |
       mon-≾FunEnv δ₁ τ≾τ′
... | ind₀ | ind₁ = ⇒-IfThenElse-tt ind₀ ind₁

mon-≾FunEnv (⇒-IfThenElse-ff δ₀ δ₁) τ≾τ′
  with mon-≾FunEnv δ₀ τ≾τ′ |
       mon-≾FunEnv δ₁ τ≾τ′
... | ind₀ | ind₁ = ⇒-IfThenElse-ff ind₀ ind₁

mon-≾FunEnv (⇒-App {f = f} δ₀ δ₁) τ≾τ′
  with τ≾τ′ f
... | eq , τf≾τ′f rewrite eq
  with mon-≾FunEnv δ₀ τ≾τ′ |
       mon-≾FunEnv δ₁ τ≾τ′
... | ind₀ | ind₁ = ⇒-App ind₀ (τf≾τ′f _ _ ind₁)

mon-≾FunEnv (⇒-Let δ₀ δ₁) τ≾τ′
  with mon-≾FunEnv δ₀ τ≾τ′ |
       mon-≾FunEnv δ₁ τ≾τ′
... | ind₀ | ind₁ = ⇒-Let ind₀ ind₁

mon-≾FunEnv (⇒-Rec {f = f} δ) τ≾τ′
  with τ≾τ′ f
... | eq , τf≾τ′f = ⇒-Rec (mon-≾FunEnv δ ((≾FunEnv-update-same f τ≾τ′)))
```

Contextual equivalence:

```
_≈_ : ∀ e₀ e₁ → Set
e₀ ≈ e₁ = ∀ c x → c E[ x ↦ e₀ ] ∼ c E[ x ↦ e₁ ]
```

Contextual simulation:

```
_≼_ : ∀ e₀ e₁ → Set
e₀ ≼ e₁ = ∀ c x → c E[ x ↦ e₀ ] ≾ c E[ x ↦ e₁ ]
```

Operational simulation is a (pre-)congruence:

```
cong-≾ : e₀ ≾ e₁ → e₀ ≼ e₁

cong-≾ e₀≾e₁ (# n) x γ m δ = δ

cong-≾ e₀≾e₁ (` y) x γ m δ
  with x ≡? y
... | yes refl = e₀≾e₁ γ m δ
... | no _ = δ

cong-≾ e₀≾e₁ (c₀ + c₁) x γ _ (⇒-Add δ₀ δ₁)
  with cong-≾ e₀≾e₁ c₀ x γ _ δ₀ |
       cong-≾ e₀≾e₁ c₁ x γ _ δ₁
... | ind₀ | ind₁ = ⇒-Add ind₀ ind₁

cong-≾ e₀≾e₁ (c₀ - c₁) x γ _ (⇒-Sub δ₀ δ₁)
  with cong-≾ e₀≾e₁ c₀ x γ _ δ₀ |
       cong-≾ e₀≾e₁ c₁ x γ _ δ₁
... | ind₀ | ind₁ = ⇒-Sub ind₀ ind₁

cong-≾ e₀≾e₁ (c₀ · c₁) x γ _ (⇒-Mul δ₀ δ₁)
  with cong-≾ e₀≾e₁ c₀ x γ _ δ₀ |
       cong-≾ e₀≾e₁ c₁ x γ _ δ₁
... | ind₀ | ind₁ = ⇒-Mul ind₀ ind₁

cong-≾ e₀≾e₁ (If c₀ Then c₁ Else c₂) x γ _ (⇒-IfThenElse-tt δ₀ δ₁)
  with cong-≾ e₀≾e₁ c₀ x γ 0 δ₀ |
       cong-≾ e₀≾e₁ c₁ x γ _ δ₁
... | ind₀ | ind₁ = ⇒-IfThenElse-tt ind₀ ind₁

cong-≾ e₀≾e₁ (If c₀ Then c₁ Else c₂) x γ _ (⇒-IfThenElse-ff δ₀ δ₁)
  with cong-≾ e₀≾e₁ c₀ x _ _ δ₀ |
       cong-≾ e₀≾e₁ c₂ x _ _ δ₁
... | ind₀ | ind₁ = ⇒-IfThenElse-ff ind₀ ind₁

cong-≾ e₀≾e₁ (f $ c) x (ϱ , τ) _ (⇒-App δ₀ δ₁)
  with cong-≾ e₀≾e₁ c x _ _ δ₀
... | ind₀ = ⇒-App ind₀ δ₁

cong-≾ e₀≾e₁ (Let y ≔ c₀ In c₁) x γ _ δ
  with x ≡? y | δ
... | yes refl | ⇒-Let δ₀ δ₁ = ⇒-Let (cong-≾ e₀≾e₁ c₀ x _ _ δ₀) δ₁
... | no _ | ⇒-Let δ₀ δ₁ = ⇒-Let (cong-≾ e₀≾e₁ c₀ x _ _ δ₀) (cong-≾ e₀≾e₁ c₁ x _ _ δ₁)

cong-≾ e₀≾e₁ (Rec g [ y ]≔ c₀ In c₁) x γ m δ
  with x ≡? y | δ
... | yes refl | ⇒-Rec δ′ = ⇒-Rec (cong-≾ e₀≾e₁ c₁ x _ _ δ′)
... | no _ | ⇒-Rec {τ = τ} δ′
  with cong-≾ e₀≾e₁ c₁ x _ _ δ′
... | ind = ⇒-Rec (mon-≾FunEnv ind (≾FunEnv-update-1 g (cong-≾ e₀≾e₁ c₀ x)))
```

```
fa0 : e₀ ≈ e₁ → e₀ ∼ e₁
fa0 e₀≈e₁ γ n = e₀≈e₁ (` x₀) x₀ γ n
```


```
fa1 : e₀ ∼ e₁ → e₀ ≈ e₁
fa1 e₀∼e₁ c x γ m = cong-≾ (∼→≾ e₀∼e₁) c x γ m , cong-≾ (∼→≾ (sym-∼ e₀∼e₁)) c x γ m
```

The denotational semantics is fully abstract:

```
full-abstraction : e₀ ≈ e₁ ↔ e₀ ∼ e₁
full-abstraction = fa0 , fa1
```

# Eager evaluation with static binding

# Lazy evaluation with dynamic binding

# Lazy evaluation with static binding
