---
title: "Gentzen's sequent calculus 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas  #-}

open import part0.index

module part1.SequentCalculus (n′ : ℕ) where
open import part1.NaturalDeduction n′ public hiding (_⊢ND_) renaming (_⊢_ to _⊢ND_) 

private
  variable
    p q r : PropName
    φ ψ θ ξ : Formula
    Γ Δ Ξ Ψ : Context
```

# Sequent calculus

```
infixr 5 _⊢_
-- infix 12 Ass_
data _⊢_ : Context → Context → Set where

    -- axiom
    Ax : [ φ ] ⊢ [ φ ]

    -- structural rules
    weakening-left : Γ ⊢ Δ →
                     ---------
                     Γ · φ ⊢ Δ

    weakening-right : Γ ⊢ Δ →
                      ---------
                      Γ ⊢ Δ · φ

    exchange-left : ∀ Γ →
                    Γ ++ [ φ ψ ] ++ Δ ⊢ Ξ →
                    -----------------------
                    Γ ++ [ ψ φ ] ++ Δ ⊢ Ξ

    exchange-right : ∀ Γ →
                     Γ ⊢ Δ ++ [ φ ψ ] ++ Ξ →
                     -----------------------
                     Γ ⊢ Δ ++ [ ψ φ ] ++ Ξ

    contraction-left : Γ · φ · φ ⊢ Δ →
                       ---------------
                       Γ · φ ⊢ Δ

    contraction-right : Γ ⊢ Δ · φ · φ →
                        ----------------
                        Γ ⊢ Δ · φ 

    -- logical rules

    ⊥-left : [ ⊥ ] ⊢ ∅

    ⊤-right : ∅ ⊢ [ ⊤ ]

    ¬-left : Γ ⊢ Δ · φ →
             -----------
             Γ · ¬ φ ⊢ Δ

    ¬-right : Γ · φ ⊢ Δ →
              ------------
              Γ ⊢ Δ · ¬ φ

    ∧-left : Γ · φ · ψ ⊢ Δ →
             -------------
             Γ · φ ∧ ψ ⊢ Δ

    ∧-right : Γ ⊢ Δ · φ →
              Γ ⊢ Δ · ψ →
              -------------
              Γ ⊢ Δ · φ ∧ ψ

    ∨-left : Γ · φ ⊢ Δ →
             Γ · ψ ⊢ Δ →
             ------------
             Γ · φ ∨ ψ ⊢ Δ

    ∨-right : Γ ⊢ Δ · φ · ψ →
              ---------------
              Γ ⊢ Δ · φ ∨ ψ

    ⇒-left : Γ ⊢ Δ · φ →
             Γ · ψ ⊢ Ξ →
             ------------------
             Γ · φ ⇒ ψ ⊢ Δ ++ Ξ

    ⇒-right : Γ · φ ⊢ Δ · ψ →
              -------------
              Γ ⊢ Δ · φ ⇒ ψ

    ⇔-left : Γ ⊢ Δ · φ · ψ →
             Γ · φ · ψ ⊢ Ξ →
             ------------------
             Γ · φ ⇔ ψ ⊢ Δ ++ Ξ

    ⇔-right : Γ · φ ⊢ Δ · ψ →
              Γ · ψ ⊢ Δ · φ →
              ---------------
              Γ ⊢ Δ · φ ⇔ ψ

    cut : Γ ⊢ Δ · φ →
          Γ · φ ⊢ Ξ →
          -----------
          Γ ⊢ Δ ++ Ξ
```

Exchange and permutations:

```
perm-left1 : ∀ Ψ → Perm Γ Δ →
             Ψ ++ Γ ⊢ Ξ →
             ----------------
             Ψ ++ Δ ⊢ Ξ

perm-left1 _ stop Ψ++Γ⊢Ξ = Ψ++Γ⊢Ξ
perm-left1 {φ ∷ Γ} {φ ∷ Δ} {Ξ} Ψ (skip π) ΨφΓ⊢Ξ
    rewrite ++-middle Ψ φ Δ = perm-left1 (Ψ ++ [ φ ]) π have where

    have : (Ψ ++ [ φ ]) ++ Γ ⊢ Ξ
    have rewrite sym (++-middle Ψ φ Γ) = ΨφΓ⊢Ξ

perm-left1 {φ ∷ ψ ∷ Γ} {ψ ∷ φ ∷ Δ} {Ξ} Ψ (swap π) ΨφψΓ⊢Ξ
    with exchange-left Ψ ΨφψΓ⊢Ξ
... | ΨψφΓ⊢Ξ = goal where

    have : (Ψ ++ [ ψ φ ]) ++ Γ ⊢ Ξ
    have rewrite sym (assoc-++ Ψ ([ ψ φ ]) Γ) = ΨψφΓ⊢Ξ

    goal : Ψ ++ [ ψ φ ] ++ Δ ⊢ Ξ
    goal rewrite sym (assoc-++ Ψ ([ ψ φ ]) Δ) = perm-left1 (Ψ ++ [ ψ φ ]) π have

perm-left1 {Γ} {Δ} {Ξ} Ψ (tran {bs = Θ} π ρ) Ψ++Γ⊢Ξ = perm-left1 Ψ ρ (perm-left1 Ψ π Ψ++Γ⊢Ξ)
```

Notice how it is crucial to generalise the context for the induction to go through.

```
perm-left : Perm Γ Δ →
            Γ ⊢ Ξ →
            ----------
            Δ ⊢ Ξ

perm-left = perm-left1 ∅
```

The proof for permutations on the right is analogous.

```
perm-right1 : ∀ Ψ →
              Perm Δ Ξ →
              Γ ⊢ Ψ ++ Δ →
              ------------
              Γ ⊢ Ψ ++ Ξ

perm-right1 {Δ} {Δ} {Γ} Ψ stop Γ⊢Ψ++Δ = Γ⊢Ψ++Δ

perm-right1 {(φ ∷ Δ)} {(φ ∷ Ξ)} {Γ} Ψ (skip π) Γ⊢Ψ++Δ
    rewrite ++-middle Ψ φ Ξ = perm-right1 (Ψ ++ [ φ ]) π have where

    have : Γ ⊢ (Ψ ++ [ φ ]) ++ Δ
    have rewrite sym (++-middle Ψ φ Δ) = Γ⊢Ψ++Δ

perm-right1 {φ ∷ ψ ∷ Δ} {ψ ∷ φ ∷ Ξ} {Γ} Ψ (swap π) Γ⊢ΨφψΔ
    with exchange-right {Ψ} Γ Γ⊢ΨφψΔ
... | Γ⊢ΨψφΔ = goal where

    have : Γ ⊢ (Ψ ++ [ ψ φ ]) ++ Δ
    have rewrite sym (assoc-++ Ψ ([ ψ φ ]) Δ) = Γ⊢ΨψφΔ

    goal : Γ ⊢ Ψ ++ [ ψ φ ] ++ Ξ
    goal rewrite sym (assoc-++ Ψ ([ ψ φ ]) Ξ) = perm-right1 (Ψ ++ [ ψ φ ]) π have

perm-right1 {Δ} {Ξ} {Γ} Ψ (tran π ρ) = perm-right1 Ψ ρ ∘ perm-right1 Ψ π 

perm-right : Perm Δ Ξ →
             Γ ⊢ Δ →
             --------
             Γ ⊢ Ξ

perm-right = perm-right1 ∅
```

```
weakening-left-SC : Γ ⊢ Ξ →
                    Γ ⊆ Δ →
                    -----------
                    Δ ⊢ Ξ

weakening-left-SC {.(_ ∷ ε)} {.(_ ∷ ε)} {Δ} Ax Γ⊆Δ = {!   !}
weakening-left-SC {.(_ ∷ _)} {Ξ} {Δ} (weakening-left Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.(_ ∷ _)} {Δ} (weakening-right Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {.(Γ ++ _ ∷ _ ∷ _)} {Ξ} {Δ} (exchange-left Γ Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.(_ ++ _ ∷ _ ∷ _)} {Δ} (exchange-right .Γ Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {.(_ ∷ _)} {Ξ} {Δ} (contraction-left Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.(_ ∷ _)} {Δ} (contraction-right Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {.(⊥ ∷ ε)} {.ε} {Δ} ⊥-left Γ⊆Δ = {!   !}
weakening-left-SC {.ε} {.(⊤ ∷ ε)} {Δ} ⊤-right Γ⊆Δ = {!   !}
weakening-left-SC {.((¬ _) ∷ _)} {Ξ} {Δ} (¬-left Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.((¬ _) ∷ _)} {Δ} (¬-right Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {.((_ ∧ _) ∷ _)} {Ξ} {Δ} (∧-left Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.((_ ∧ _) ∷ _)} {Δ} (∧-right Γ⊢Ξ Γ⊢Ξ₁) Γ⊆Δ = {!   !}
weakening-left-SC {.((_ ∨ _) ∷ _)} {Ξ} {Δ} (∨-left Γ⊢Ξ Γ⊢Ξ₁) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.((_ ∨ _) ∷ _)} {Δ} (∨-right Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {.((_ ⇒ _) ∷ _)} {.(_ ++ _)} {Δ} (⇒-left Γ⊢Ξ Γ⊢Ξ₁) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.((_ ⇒ _) ∷ _)} {Δ} (⇒-right Γ⊢Ξ) Γ⊆Δ = {!   !}
weakening-left-SC {.((_ ⇔ _) ∷ _)} {.(_ ++ _)} {Δ} (⇔-left Γ⊢Ξ Γ⊢Ξ₁) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.((_ ⇔ _) ∷ _)} {Δ} (⇔-right Γ⊢Ξ Γ⊢Ξ₁) Γ⊆Δ = {!   !}
weakening-left-SC {Γ} {.(_ ++ _)} {Δ} (cut Γ⊢Ξ Γ⊢Ξ₁) Γ⊆Δ = {!   !}

weakening-right-SC : Γ ⊢ Δ →
                     Δ ⊆ Ξ →
                     -----------
                     Γ ⊢ Ξ

weakening-right-SC Γ⊢Δ Δ⊆Ξ = {!   !}

weakening-left'-SC :
                    Γ ⊢ Δ →
                    -----------
                    Γ ++ Ξ ⊢ Δ

weakening-left'-SC {Γ} {Ξ = ε} Γ⊢Δ rewrite ++ε Γ = Γ⊢Δ
weakening-left'-SC {Γ} {Ξ = ξ ∷ Ξ} Γ⊢Δ = perm-left (π Γ) (weakening-left (weakening-left'-SC Γ⊢Δ)) where

    π : ∀ Γ → Perm (ξ ∷ Γ ++ Ξ) (Γ ++ ξ ∷ Ξ)
    π ε = stop
    π (φ ∷ Γ) =
        BEGIN
        have Perm (Γ ++ Ξ) (Γ ++ Ξ)                     by stop
        have Perm (ξ ∷ φ ∷ Γ ++ Ξ) (φ ∷ ξ ∷ Γ ++ Ξ)     apply swap at here
        have Perm (φ ∷ ξ ∷ Γ ++ Ξ) (φ ∷ Γ ++ ξ ∷ Ξ)     by skip (π Γ)
        have Perm (ξ ∷ φ ∷ Γ ++ Ξ) (φ ∷ Γ ++ ξ ∷ Ξ)     apply tran at back 1 , here
        END

Ax-left-SC_ : φ ∈ Γ →
             ---------
             Γ ⊢ [ φ ]

Ax-left-SC_ {Γ = φ ∷ Ξ} here = weakening-left'-SC Ax
Ax-left-SC_ (there φ∈Γ) = weakening-left (Ax-left-SC φ∈Γ)

-- Ax-SC : φ ∈ Γ →
--         φ ∈ Δ →
--         --------
--         Γ ⊢ Δ

-- Ax-SC φ∈Γ φ∈Δ = {! φ∈Γ  !}
```

We simulate natural deduction with sequent calculus.
The non-trivial cases are the eliminations.
This is where the cut rule is used.

```
_⊢SC_ = _⊢_

-- elim-SC : 

ND→SC : Γ ⊢ND φ →
        -----------
        Γ ⊢SC [ φ ]
        
ND→SC (Ass φ∈Γ) = Ax-left-SC φ∈Γ

ND→SC ⊤I = weakening-left'-SC ⊤-right

ND→SC (⇒I Γ·φ⊢NDψ)
    with ND→SC Γ·φ⊢NDψ
... | Γ·φ⊢ψ = ⇒-right Γ·φ⊢ψ

-- non-trivial case
ND→SC {Γ} {ψ} (⇒E {φ = φ} Γ⊢NDφ⇒ψ Γ⊢NDφ)
    with ND→SC Γ⊢NDφ⇒ψ | ND→SC Γ⊢NDφ
... | Γ⊢φ⇒ψ | Γ⊢φ =
    BEGIN
    have [ ψ ] ⊢ [ ψ ]      by Ax
    have Γ · ψ ⊢ [ ψ ]      apply weakening-left'-SC at here
    have Γ ⊢ [ φ ]          by Γ⊢φ
    have Γ · φ ⇒ ψ ⊢ [ ψ ]  apply ⇒-left at here , back 1
    have Γ ⊢ [ (φ ⇒ ψ) ]    by Γ⊢φ⇒ψ
    have Γ ⊢ [ ψ ]          apply cut at here , back 1 -- cut!
    END

ND→SC (∧I Γ⊢NDφ Γ⊢NDψ)
    with ND→SC Γ⊢NDφ | ND→SC Γ⊢NDψ
... | Γ⊢φ | Γ⊢ψ = ∧-right Γ⊢φ Γ⊢ψ

ND→SC {Γ} {φ} (∧E-left {ψ = ψ} Γ⊢NDφ∧ψ)
    with ND→SC Γ⊢NDφ∧ψ
... | Γ⊢φ∧ψ =
    BEGIN
    have Γ · φ · ψ ⊢ [ φ ]      by Ax-left-SC back 1
    have Γ · φ ∧ ψ ⊢ [ φ ]      apply ∧-left at here
    have Γ ⊢ [ (φ ∧ ψ) ]        by Γ⊢φ∧ψ
    have Γ ⊢ [ φ ]              apply cut at here , back 1 -- cut!
    END

ND→SC {Γ} {ψ} (∧E-right {φ = φ} Γ⊢NDφ∧ψ)
    with ND→SC Γ⊢NDφ∧ψ
... | Γ⊢φ∧ψ =
    BEGIN
    have Γ · φ · ψ ⊢ [ ψ ]      by Ax-left-SC here
    have Γ · φ ∧ ψ ⊢ [ ψ ]      apply ∧-left at here
    have Γ ⊢ [ (φ ∧ ψ) ]        by Γ⊢φ∧ψ
    have Γ ⊢ [ ψ ]              apply cut at here , back 1 -- cut!
    END

ND→SC {Γ} {φ ∨ ψ} (∨I-left Γ⊢NDφ)
    with ND→SC Γ⊢NDφ
... | Γ⊢φ =
    BEGIN
    have Γ ⊢ [ φ ]          by Γ⊢φ
    have Γ ⊢ ∅ · φ · ψ      apply weakening-right at here
    have Γ ⊢ [ (φ ∨ ψ) ]    apply ∨-right at here
    END

ND→SC {Γ} {φ ∨ ψ} (∨I-right Γ⊢NDψ)
    with ND→SC Γ⊢NDψ
... | Γ⊢ψ =
    BEGIN
    have Γ ⊢ [ ψ ]          by Γ⊢ψ
    have [ ψ ] ⊆ ∅ · φ · ψ  by (λ{here → here}) -- can we mechanise this check? (inclusion of two given finite lists)
    have Γ ⊢ ∅ · φ · ψ      apply weakening-right-SC at back 1 , here
    have Γ ⊢ [ (φ ∨ ψ) ]    apply ∨-right at here
    END

ND→SC (∨E {Γ} {φ} {ψ} {θ} Γ⊢NDφ∨ψ Γ·φ⊢NDθ Γ·ψ⊢NDθ)
    with ND→SC Γ⊢NDφ∨ψ | ND→SC Γ·φ⊢NDθ | ND→SC Γ·ψ⊢NDθ
... | Γ⊢φ∨ψ | Γ·φ⊢θ | Γ·ψ⊢θ = 
    BEGIN
    have Γ · φ ⊢ [ θ ]          by Γ·φ⊢θ
    have Γ · ψ ⊢ [ θ ]          by Γ·ψ⊢θ
    have Γ · φ ∨ ψ ⊢ [ θ ]      apply ∨-left at back 1 , here
    have Γ ⊢ [ (φ ∨ ψ) ]        by Γ⊢φ∨ψ
    have Γ ⊢ [ θ ]              apply cut at here , back 1 -- cut!
    END

ND→SC {Γ} {φ} (⊥E Γ⊢ND⊥)
    with ND→SC Γ⊢ND⊥
... | Γ⊢⊥ =
    BEGIN
    have [ ⊥ ] ⊢ ∅         by ⊥-left
    have [ ⊥ ] ⊢ [ φ ]     apply weakening-right at here
    have Γ · ⊥ ⊢ [ φ ]     apply weakening-left'-SC at here
    have Γ ⊢ [ ⊥ ]         by Γ⊢⊥
    have Γ ⊢ [ φ ]         apply cut at here , back 1
    END

ND→SC {Γ} {φ} (⊥⊥E Γ⊢NDφ⇒⊥⇒⊥)
    with ND→SC Γ⊢NDφ⇒⊥⇒⊥
... | Γ⊢φ⇒⊥⇒⊥ =
    BEGIN
    have [ φ ] ⊢ [ φ ]                  by Ax
    have Γ · φ ⊢ [ φ ]                  apply weakening-left'-SC at here
    have Γ · φ ⊢ ∅ · φ · ⊥             apply weakening-right at here
    have Γ ⊢ ∅ · φ · φ ⇒ ⊥             apply ⇒-right at here

    have [ ⊥ ] ⊢ ∅                    by ⊥-left
    have [ ⊥ ] ⊢ [ φ ]                apply weakening-right at here
    have Γ · ⊥ ⊢ [ φ ]                apply weakening-left'-SC at here
    have Γ · (φ ⇒ ⊥) ⇒ ⊥ ⊢ ∅ · φ · φ  apply ⇒-left at back 3 , here
    have Γ · (φ ⇒ ⊥) ⇒ ⊥ ⊢ [ φ ]      apply contraction-right at here
    have Γ ⊢ [ ((φ ⇒ ⊥) ⇒ ⊥) ]        by Γ⊢φ⇒⊥⇒⊥
    have Γ ⊢ [ φ ]                     apply cut at here , back 1
    END

ND→SC {Γ} {¬ φ} (¬I Γ⊢NDφ⇒⊥)
    with ND→SC Γ⊢NDφ⇒⊥
... | Γ⊢φ⇒⊥ =
    BEGIN
    have Γ · φ · ⊥ ⊢ ∅              by weakening-left'-SC ⊥-left
    have Γ · φ ⊢ [ φ ]              by weakening-left'-SC Ax
    have Γ · φ · φ ⇒ ⊥ ⊢ ∅          apply ⇒-left at here , back 1
    have Γ ⊢ [ (φ ⇒ ⊥) ]            by Γ⊢φ⇒⊥
    have Γ · φ ⊢ [ (φ ⇒ ⊥) ]        apply weakening-left at here

    have Γ · φ ⊢ ∅                  apply cut at here , back 2
    have Γ ⊢ [ (¬ φ) ]              apply ¬-right at here
    END

ND→SC {Γ} {φ ⇒ ⊥} (¬E Γ⊢ND¬φ)
    with ND→SC Γ⊢ND¬φ
... | Γ⊢¬φ =
    BEGIN
    have Γ · φ ⊢ [ φ ]            by Ax-left-SC here
    have [ φ ] ⊆ ∅ · ⊥ · φ        by (λ{here → here}) -- can this inclusion check be automated?
    have Γ · φ ⊢ ∅ · ⊥ · φ        apply weakening-right-SC at back 1 , here
    have Γ · φ · ¬ φ ⊢ [ ⊥ ]      apply ¬-left at here
    have Γ ⊢ [ (¬ φ) ]            by Γ⊢¬φ
    have Γ · φ ⊢ [ (¬ φ) ]        apply weakening-left at here
    have Γ · φ ⊢ [ ⊥ ]            apply cut at here , back 2
    have Γ ⊢ [ (φ ⇒ ⊥) ]          apply ⇒-right at here
    END

ND→SC {Γ} {φ ⇔ ψ} (⇔I Γ⊢NDφ⇒ψ∧ψ⇒φ)
    with ND→SC Γ⊢NDφ⇒ψ∧ψ⇒φ
... | Γ⊢φ⇒ψ∧ψ⇒φ =
    BEGIN
    have Γ ⊢ [ ((φ ⇒ ψ) ∧ (ψ ⇒ φ)) ]        by Γ⊢φ⇒ψ∧ψ⇒φ
    have Γ · φ ⊢ [ ((φ ⇒ ψ) ∧ (ψ ⇒ φ)) ]    apply weakening-left at here

    have Γ · φ  ⊢ [ φ ]                     by Ax-left-SC here
    have Γ · φ · ψ ⊢ [ ψ ]                  by Ax-left-SC here
    have Γ · φ · φ ⇒ ψ ⊢ [ ψ ]              apply ⇒-left at back 1 , here
    have Γ · φ · φ ⇒ ψ · ψ ⇒ φ ⊢ [ ψ ]      apply weakening-left at here
    have Γ · φ · (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⊢ [ ψ ]  apply ∧-left at here

    have Γ · φ ⊢ [ ψ ]                      apply cut at back 5 , here

    have Γ · ψ ⊢ [ ((φ ⇒ ψ) ∧ (ψ ⇒ φ)) ]    apply weakening-left at back 7

    have Γ · ψ ⊢ [ ψ ]                      by Ax-left-SC here
    have Γ · ψ · φ ⇒ ψ ⊢ [ ψ ]              apply weakening-left at here
    have Γ · ψ · φ ⇒ ψ · φ ⊢ [ φ ]          by Ax-left-SC here

    have Γ · ψ · φ ⇒ ψ · ψ ⇒ φ ⊢ [ φ ]      apply ⇒-left at back 1 , here
    have Γ · ψ · (φ ⇒ ψ) ∧ (ψ ⇒ φ) ⊢ [ φ ]  apply ∧-left at here
    have Γ · ψ ⊢ [ φ ]                      apply cut at back 5 , here

    have Γ ⊢ [ (φ ⇔ ψ) ]                    apply ⇔-right at back 7 , here
    END

ND→SC {Γ} {(φ ⇒ ψ) ∧ (ψ ⇒ φ)} (⇔E Γ⊢NDφ⇔ψ)
    with ND→SC Γ⊢NDφ⇔ψ
... | Γ⊢φ⇔ψ =
    BEGIN
    have Γ ⊢ [ (φ ⇔ ψ) ]                    by Γ⊢φ⇔ψ
    have Γ · φ ⊢ [ (φ ⇔ ψ) ]                apply weakening-left at here
    have Γ · φ ⊢ ∅ · φ · ψ                  by weakening-right (Ax-left-SC here)
    have Γ · φ · φ · ψ ⊢ [ ψ ]              by Ax-left-SC here
    have Γ · φ · φ ⇔ ψ ⊢ [ ψ ]              apply ⇔-left at back 1 , here
    have Γ · φ ⊢ [ ψ ]                      apply cut at back 3 , here
    have Γ ⊢ [ (φ ⇒ ψ) ]                    apply ⇒-right at here

    have Γ · ψ ⊢ [ (φ ⇔ ψ) ]                apply weakening-left at back 6
    have Γ · ψ ⊢ ∅ · φ · ψ                  by weakening-right-SC (Ax-left-SC here) (λ{here → here}) 
    have Γ · ψ · φ · ψ ⊢ [ φ ]              by weakening-left (Ax-left-SC here)
    have Γ · ψ · φ ⇔ ψ ⊢ [ φ ]              apply ⇔-left at back 1 , here
    have Γ · ψ ⊢ [ φ ]                      apply cut at back 3 , here
    have Γ ⊢ [ (ψ ⇒ φ) ]                    apply ⇒-right at here

    have Γ ⊢ [ ((φ ⇒ ψ) ∧ (ψ ⇒ φ)) ]        apply ∧-right at back 6 , here
    END
```

We simulate sequent calculus with natural deduction.
Since natural deduction takes a single formula on the right,
we take the disjunction of all formulas of the right haalf of a sequent.

```
SC→ND : Γ ⊢SC Δ →
        -----------
        Γ ⊢ND ⋁ Δ

SC→ND Ax = Ass here

SC→ND (weakening-left Γ⊢Δ)
    with SC→ND Γ⊢Δ
... | Γ⊢NDΔ = weakening-ND Γ⊢NDΔ there

SC→ND {Γ} {φ ∷ Δ} (weakening-right Γ⊢Δ)
    with SC→ND Γ⊢Δ
... | Γ⊢NDΔ
    with Δ 
... | ε = ⊥E Γ⊢NDΔ
... | _ ∷ _ = ∨I-right Γ⊢NDΔ

SC→ND (exchange-left {φ} {ψ} {Δ} {Ξ} Γ ΓφψΔ⊢Ξ)
    with SC→ND ΓφψΔ⊢Ξ 
... | ΓφψΔ⊢NDΞ = perm-ND-left (swap-deep Γ) ΓφψΔ⊢NDΞ

SC→ND (exchange-right {Δ} {φ} {ψ} {Ξ} Γ Γ⊢ΔφψΞ)
    with SC→ND Γ⊢ΔφψΞ
... | Γ⊢NDΔφψΞ = perm-ND-right (swap-deep Δ) Γ⊢NDΔφψΞ

SC→ND (contraction-left Γφφ⊢Δ)
    with SC→ND Γφφ⊢Δ
... | Γφφ⊢NDΔ = contraction-ND-left Γφφ⊢NDΔ

SC→ND {Δ = φ ∷ Δ} (contraction-right Γ⊢Δφφ)
    with SC→ND Γ⊢Δφφ
... | Γ⊢NDΔφφ = contraction-ND-right Δ Γ⊢NDΔφφ

SC→ND ⊥-left = Ass here

SC→ND ⊤-right = ⊤I

SC→ND (¬-left {Γ} {Δ} {φ} Γ⊢Δ·φ)
    with SC→ND Γ⊢Δ·φ
... | Γ⊢NDΔ∨φ
    with Δ
... | ε =
    BEGIN
    have Γ ⊢ND φ            by Γ⊢NDΔ∨φ
    have Γ ⊆ Γ · ¬ φ        by there
    have Γ · ¬ φ ⊢ND φ      apply weakening-ND at back 1 , here
    have Γ · ¬ φ ⊢ND ¬ φ    by Ass here
    have Γ · ¬ φ ⊢ND φ ⇒ ⊥  apply ¬E at here
    have Γ · ¬ φ ⊢ND ⊥      apply ⇒E at here , back 2
    END

... | Ξ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND φ ∨ (⋁ Ξ)            by Γ⊢NDΔ∨φ
    have Γ ⊆ Γ · ¬ φ                by there
    have Γ · ¬ φ ⊢ND φ ∨ (⋁ Ξ)      apply weakening-ND at back 1 , here

    have Γ · ¬ φ · φ ⊢ND φ          by Ass here
    have Γ · ¬ φ · φ ⊢ND ¬ φ        by Ass back 1
    have Γ · ¬ φ · φ ⊢ND φ ⇒ ⊥      apply ¬E at here
    have Γ · ¬ φ · φ ⊢ND ⊥          apply ⇒E at here , back 2

    have Γ · ¬ φ · φ ⊢ND ⋁ Ξ        apply ⊥E at here

    have Γ · ¬ φ · (⋁ Ξ) ⊢ND ⋁ Ξ    by Ass here

    have Γ · ¬ φ ⊢ND ⋁ Ξ            apply ∨E at back 6 , back 1 , here
    END

SC→ND (¬-right {Γ} {φ} {Δ} Γ·φ⊢Δ)
    with SC→ND Γ·φ⊢Δ
... | Γ·φ⊢ND⋁Δ
    with Δ
... | ε =
    BEGIN
    have Γ · φ ⊢ND ⊥    by Γ·φ⊢ND⋁Δ
    have Γ ⊢ND φ ⇒ ⊥    apply ⇒I at here
    have Γ ⊢ND ¬ φ      apply ¬I at here
    END

... | Ξ@(_ ∷ _) =
    BEGIN
    have Γ · φ ⊢ND ⋁ Ξ                      by Γ·φ⊢ND⋁Δ
    have Γ · φ ⊢ND ¬ φ ∨ (⋁ Ξ)              apply ∨I-right at here
    
    have Γ · φ ⇒ ⊥ ⊢ND φ ⇒ ⊥                by Ass here 
    have Γ · φ ⇒ ⊥ ⊢ND ¬ φ                  apply ¬I at here
    have Γ · φ ⇒ ⊥ ⊢ND ¬ φ ∨ (⋁ Ξ)          apply ∨I-left at here
    
    have Γ ⊢ND ¬ φ ∨ (⋁ Ξ)                  apply case-split at back 3 , here 
    END

SC→ND (∧-left {Γ} {φ} {ψ} {Δ} Γφψ⊢Δ)
    with SC→ND Γφψ⊢Δ
... | Γφψ⊢ND⋁Δ = ∧-left-ND Γφψ⊢ND⋁Δ

SC→ND (∧-right {Γ} {Δ} {φ} {ψ} Γ⊢Δ·φ Γ⊢Δ·ψ)
    with SC→ND Γ⊢Δ·φ | SC→ND Γ⊢Δ·ψ
... | Γ⊢ND⋁Δφ | Γ⊢ND⋁Δψ
    with Δ
... | ε =
    BEGIN
    have Γ ⊢ND φ            by Γ⊢ND⋁Δφ
    have Γ ⊢ND ψ            by Γ⊢ND⋁Δψ
    have Γ ⊢ND φ ∧ ψ        apply ∧I at back 1 , here
    END

... | Ξ@(_ ∷ _ ) =
    BEGIN
    have Γ ⊢ND φ ∨ (⋁ Ξ)                        by Γ⊢ND⋁Δφ
    have Γ · (⋁ Ξ) ⇒ ⊥ ⊢ND φ                    apply swap-Neg-Or-ND at here

    have Γ ⊢ND ψ ∨ (⋁ Ξ)                        by Γ⊢ND⋁Δψ
    have Γ · (⋁ Ξ) ⇒ ⊥ ⊢ND ψ                    apply swap-Neg-Or-ND at here

    have Γ · (⋁ Ξ) ⇒ ⊥ ⊢ND φ ∧ ψ                apply ∧I at back 2 , here
    have Γ · (⋁ Ξ) ⇒ ⊥ ⊢ND φ ∧ ψ ∨ (⋁ Ξ)        apply ∨I-left at here

    have Γ · (⋁ Ξ) ⊢ND ⋁ Ξ                      by Ass here
    have Γ · (⋁ Ξ) ⊢ND φ ∧ ψ ∨ (⋁ Ξ)            apply ∨I-right at here

    have Γ ⊢ND φ ∧ ψ ∨ (⋁ Ξ)                    apply case-split at here , back 2
    END

SC→ND (∨-left {Γ} {φ} {Δ} {ψ} Γ·φ⊢Δ Γ·ψ⊢Δ)
    with SC→ND Γ·φ⊢Δ | SC→ND Γ·ψ⊢Δ
... | Γ·φ⊢ND⋁Δ | Γ·ψ⊢ND⋁Δ = ∨-left-ND Γ·φ⊢ND⋁Δ Γ·ψ⊢ND⋁Δ

SC→ND (∨-right {Γ} {Δ} {φ} {ψ} Γ⊢Δ·φ·ψ)
    with SC→ND Γ⊢Δ·φ·ψ
... | Γ⊢NDΔ·φ·ψ
    with Δ
... | ε = ⇒E commOr-ND Γ⊢NDΔ·φ·ψ

... | Ξ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND ψ ∨ φ ∨ (⋁ Ξ)                        by Γ⊢NDΔ·φ·ψ
    have Γ ⊢ND (ψ ∨ φ) ∨ (⋁ Ξ)                      apply assocOr-ND at here
    have Γ ⊢ND (ψ ∨ φ) ⇒ (φ ∨ ψ)                    by commOr-ND
    have Γ ⊢ND (φ ∨ ψ) ∨ (⋁ Ξ)                      apply attachOr-ND at back 1 , here
    END

SC→ND (⇒-left {Γ} {Δ} {φ} {ψ} {Ξ} Γ⊢Δ·φ Γ·ψ⊢Ξ)
    with SC→ND Γ⊢Δ·φ | SC→ND Γ·ψ⊢Ξ
... | Γ⊢NDΔ·φ | Γ·ψ⊢NDΞ
    with Δ
... | ε =
    BEGIN
    have Γ ⊢ND φ                    by Γ⊢NDΔ·φ
    have Γ ⊆ Γ · φ ⇒ ψ              by there
    have Γ · φ ⇒ ψ ⊢ND φ            apply weakening-ND at back 1 , here
    have Γ · φ ⇒ ψ ⊢ND φ ⇒ ψ        by Ass here
    have Γ · φ ⇒ ψ ⊢ND ψ            apply ⇒E at here , back 1

    have Γ · ψ ⊢ND ⋁ Ξ              by Γ·ψ⊢NDΞ
    have Γ ⊢ND ψ ⇒ (⋁ Ξ)            apply DT2-ND at here
    have Γ · φ ⇒ ψ ⊢ND ψ ⇒ (⋁ Ξ)    apply weakening-ND at here , back 5
    have Γ · φ ⇒ ψ ⊢ND ⋁ Ξ          apply ⇒E at here , back 3
    END
    
... | Ψ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND φ ∨ (⋁ Ψ)                    by Γ⊢NDΔ·φ
    have Γ · ψ ⊢ND ⋁ Ξ                      by Γ·ψ⊢NDΞ
    have Γ · φ ⇒ ψ ⊢ND (⋁ Ψ) ∨ (⋁ Ξ)        apply ⇒-left-ND at back 1 , here
    have Γ · φ ⇒ ψ ⊢ND ⋁ (Ψ ++ Ξ)           apply longDisjunction-++-ND Ψ at here
    END

SC→ND (⇒-right {Γ} {φ} {Δ} {ψ} Γ·φ⊢Δ·ψ)
    with SC→ND Γ·φ⊢Δ·ψ
... | Γ·φ⊢NDΔ·ψ
    with Δ
... | ε = ⇒I Γ·φ⊢NDΔ·ψ
... | Ψ@(_ ∷ _) = ⇒-right-ND Γ·φ⊢NDΔ·ψ

SC→ND (⇔-left {Γ} {Δ} {φ} {ψ} {Ξ} Γ⊢Δ·φ·ψ Γ·φ·ψ⊢Ξ)
    with SC→ND Γ⊢Δ·φ·ψ | SC→ND Γ·φ·ψ⊢Ξ
... | Γ⊢NDΔ·φ·ψ | Γ·φ·ψ⊢NDΞ
    with Δ
... | ε = ⇔-left-ND Γ⊢NDΔ·φ·ψ Γ·φ·ψ⊢NDΞ

... | Ψ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND ψ ∨ φ ∨ (⋁ Ψ)                by Γ⊢NDΔ·φ·ψ
    have Γ · φ · ψ ⊢ND ⋁ Ξ                  by Γ·φ·ψ⊢NDΞ
    have Γ · φ ⇔ ψ ⊢ND (⋁ Ψ) ∨ (⋁ Ξ)        apply ⇔-left'-ND at back 1 , here
    have Γ · φ ⇔ ψ ⊢ND ⋁ (Ψ ++ Ξ)           apply longDisjunction-++-ND Ψ at here
    END

SC→ND (⇔-right {Γ} {φ} {Δ} {ψ} Γ·φ⊢Δ·ψ Γ·ψ⊢Δ·φ)
    with SC→ND Γ·φ⊢Δ·ψ | SC→ND Γ·ψ⊢Δ·φ
... | Γ·φ⊢NDΔ·ψ | Γ·ψ⊢NDΔ·φ
    with Δ
... | ε = ↔-right-ND Γ·φ⊢NDΔ·ψ Γ·ψ⊢NDΔ·φ

... | Ψ@(_ ∷ _) = ↔-right'-ND Γ·φ⊢NDΔ·ψ Γ·ψ⊢NDΔ·φ

SC→ND (cut {Γ} {Δ} {φ} {Ξ} Γ⊢Δ·φ Γ·φ⊢Ξ)
    with SC→ND Γ⊢Δ·φ | SC→ND Γ·φ⊢Ξ
... | Γ⊢NDΔ·φ | Γ·φ⊢NDΞ
    with Δ
... | ε =
    BEGIN
    have Γ ⊢ND φ            by Γ⊢NDΔ·φ
    have Γ · φ ⊢ND ⋁ Ξ      by Γ·φ⊢NDΞ
    have Γ ⊢ND φ ⇒ (⋁ Ξ)    apply ⇒I at here
    have Γ ⊢ND ⋁ Ξ          apply ⇒E at here , back 2
    END

... | Ψ@(_ ∷ _) =
    BEGIN
    have Γ ⊢ND φ ∨ (⋁ Ψ)           by Γ⊢NDΔ·φ
    have Γ · φ ⊢ND ⋁ Ξ             by Γ·φ⊢NDΞ
    have Γ ⊢ND (⋁ Ψ) ∨ (⋁ Ξ)       apply cut-ND at back 1 , here
    have Γ ⊢ND ⋁ (Ψ ++ Ξ)          apply longDisjunction-++-ND Ψ at here
    END
```

# Soundness and completeness

```
soundness-SC : Γ ⊢ Δ →
               --------
               Γ ⊨ ⋁ Δ

soundness-SC Γ⊢Δ = soundness-ND (SC→ND Γ⊢Δ)

completeness-SC : Γ ⊨ φ →
                  ----------
                  Γ ⊢ [ φ ]

completeness-SC Γ⊨⋁Δ = ND→SC (completeness-ND Γ⊨⋁Δ)
```