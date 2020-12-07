---
title: "Permutationss 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.Permutations where
open import part0.List public
open import part0.TList public

private
  variable
    ℓ : Level
    A : Set ℓ
    a b : A
    as bs cs : A *


data Perm {ℓ} {A : Set ℓ} : A * → A * → Set ℓ where
  stop : Perm as as
  skip : Perm as bs → Perm (a ∷ as) (a ∷ bs)
  swap : Perm as bs → Perm (a ∷ b ∷ as) (b ∷ a ∷ bs)
  tran : Perm as bs → Perm bs cs → Perm as cs

-- _∼_ : ∀ {ℓ} {A : Set ℓ} → A * → A * → Set ℓ
-- as ∼ bs = Perm as bs

sym-perm : Perm as bs → Perm bs as
sym-perm perm = {!!}

perm-ε : Perm ε as → as ≡ ε
perm-ε stop = refl
perm-ε (tran π ρ)
  with perm-ε π
... | eq-π rewrite eq-π
  with perm-ε ρ
... | eq-ρ = eq-ρ

perm-singleton : Perm ([ a ]) bs → bs ≡ [ a ]
perm-singleton stop = refl
perm-singleton (skip π) rewrite perm-ε π = refl
perm-singleton (tran π ρ)
  with perm-singleton π
... | eq-π rewrite eq-π
  with perm-singleton ρ
... | eq-ρ = eq-ρ

swap-deep : ∀ (as : A *) → Perm (as ++ a ∷ b ∷ bs) (as ++ b ∷ a ∷ bs)
swap-deep ε = swap stop
swap-deep (a ∷ as) = skip (swap-deep as)

--⊆-perm : as ⊆ bs → ∃[ cs ] ∃[ ds ] 

perm-middle : ∀ {ℓ} {A : Set ℓ} {a : A} {bs : A *} (as : A *) → Perm (a ∷ as ++ bs) (as ++ a ∷ bs)
perm-middle ε = stop
perm-middle {ℓ} {A} {a} {bs} (b ∷ as) =
    BEGIN
        have Perm (as ++ bs) (as ++ bs)                     by stop
        have Perm (a ∷ b ∷ as ++ bs) (b ∷ a ∷ as ++ bs)     apply swap at here
        have Perm (b ∷ a ∷ as ++ bs) (b ∷ as ++ a ∷ bs)     by skip (perm-middle as)
        have Perm (a ∷ b ∷ as ++ bs) (b ∷ as ++ a ∷ bs)     apply tran at back 1 , here
    END
```