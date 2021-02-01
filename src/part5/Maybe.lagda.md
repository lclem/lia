---
title: "The Maybe monad 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Maybe where
open import part0.index -- hiding (AExp; A⟦_⟧; _≈_; _⊑_; _$_; trans-⊑; refl-⊑) renaming (_+_ to _+ℕ_; _*_ to _·ℕ_; _∸_ to _-ℕ_; _≤_ to _≤ℕ_) public
```


```
private
    variable
        ℓ m n o : Level
        A : Set ℓ
        B : Set m
        C : Set n
        D : Set o

data Maybe (A : Set ℓ) : Set ℓ where
  Nothing : Maybe A
  Just : A → Maybe A

infix 10 ⌊_⌋
pattern ⊥ = Nothing
pattern ⌊_⌋ a = Just a

private
    variable
        A⊥ : Maybe A
        B⊥ : Maybe B
        C⊥ : Maybe C
        a : A
        a⊥ : Maybe A
```

```
lift : (A → A) → Maybe A → Maybe A
lift f ⊥ = ⊥
lift f ⌊ a ⌋ = ⌊ f a ⌋

lift2 : (A → B → C) → Maybe A → Maybe B → Maybe C
lift2 f ⊥ _ = ⊥
lift2 f _ ⊥ = ⊥
lift2 f ⌊ a ⌋ ⌊ b ⌋ = ⌊ f a b ⌋

lift⊥ : (A → Maybe B) → Maybe A → Maybe B
lift⊥ f ⊥ = ⊥
lift⊥ f ⌊ a ⌋ = f a

lift2⊥ : (A → B → Maybe C) → Maybe A → Maybe B → Maybe C
lift2⊥ f ⊥ _ = ⊥
lift2⊥ f _ ⊥ = ⊥
lift2⊥ f ⌊ a ⌋ ⌊ b ⌋ = f a b

lift3⊥ : (A → B → C → Maybe D) → Maybe A → Maybe B → Maybe C → Maybe D
lift3⊥ f ⊥ _ _ = ⊥
lift3⊥ f _ ⊥ _ = ⊥
lift3⊥ f _ _ ⊥ = ⊥
lift3⊥ f ⌊ a ⌋ ⌊ b ⌋ ⌊ c ⌋ = f a b c
```

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