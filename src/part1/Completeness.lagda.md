---
title: "Completeness of Hilbert-style proof systems for propositional logic 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-} -- --rewriting --confluence-check
open import part0.index

module part1.Completeness (n′ : ℕ) where
open import part1.CharacteristicFormulas n′ hiding (¬_; ϱtt; ϱff)

private
  variable
    φ ψ θ : Formula
    Γ Δ : Context
```

References:

* Proof pearl @CaiKaposiAltenkirch:2015 for propositional logic.
* modal logic S5 @Bentzen:arXiv:2019.


## Proof system

```

infix 99 ¬_
¬_ : Formula → Formula
¬ φ = φ ⇒ ⊥

infixr 5 _⊢_
data _⊢_ : Context → Formula → Set where

  -- assumption
  Ass : φ ∈ Γ → Γ ⊢ φ

  -- axioms
  A1 : Γ ⊢ φ ⇒ ψ ⇒ φ -- projection
  A2 : Γ ⊢ (φ ⇒ ψ ⇒ θ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ θ -- transitivity
  A3 : Γ ⊢ ¬ ¬ φ ⇒ φ -- double negation

  -- modus ponens
  MP : Δ ⊢ φ ⇒ ψ → Δ ⊢ φ → Δ ⊢ ψ
```

A proof example.

```
B0 : ∀ {Δ φ} → Δ ⊢ φ ⇒ φ
B0 {Δ} {φ} = S5 where

  S1 : Δ ⊢ φ ⇒ φ ⇒ φ
  S1 = A1

  S2 : Δ ⊢ φ ⇒ (φ ⇒ φ) ⇒ φ
  S2 = A1

  S3 : Δ ⊢ (φ ⇒ (φ ⇒ φ) ⇒ φ) ⇒ (φ ⇒ φ ⇒ φ) ⇒ φ ⇒ φ
  S3 = A2

  S4 : Δ ⊢ (φ ⇒ φ ⇒ φ) ⇒ φ ⇒ φ
  S4 = MP S3 S2

  S5 : Δ ⊢ φ ⇒ φ
  S5 = MP S4 S1
```

## Monotonicity

```
monotonicityOfProofs1 : Δ ⊢ φ → Δ · ψ ⊢ φ
monotonicityOfProofs1 (Ass φ∈Δ) = Ass (there φ∈Δ)
monotonicityOfProofs1 A1 = A1
monotonicityOfProofs1 A2 = A2
monotonicityOfProofs1 A3 = A3
monotonicityOfProofs1 (MP Δ⊢φ Δ⊢ψ) = MP (monotonicityOfProofs1 Δ⊢φ) (monotonicityOfProofs1 Δ⊢ψ)
```

## Deduction theorem

```
dt1 : Δ ⊢ φ ⇒ ψ → φ ∷ Δ ⊢ ψ
dt1 {Δ} {φ} {ψ} Δ⊢φ⇒ψ = MP Δ,φ⊢φ⇒ψ Δ,φ⊢φ where

  Δ,φ⊢φ⇒ψ : φ ∷ Δ ⊢ φ ⇒ ψ
  Δ,φ⊢φ⇒ψ = monotonicityOfProofs1 {ψ = φ} Δ⊢φ⇒ψ

  Δ,φ⊢φ : φ ∷ Δ ⊢ φ
  Δ,φ⊢φ = Ass here

dt2 : Δ · φ ⊢ ψ →
      ----------
      Δ ⊢ φ ⇒ ψ

dt2 (Ass here) = B0
dt2 (Ass (there ψ∈Δ)) = MP A1 (Ass ψ∈Δ)
dt2 A1 = MP A1 A1
dt2 A2 = MP A1 A2
dt2 A3 = MP A1 A3
dt2 {Δ} {φ} {ψ} (MP {φ = ξ} φ,Δ⊢ξ⇒ψ φ,Δ⊢ξ) = SS where

  S1 : Δ ⊢ φ ⇒ ξ
  S1 = dt2 φ,Δ⊢ξ

  S2 : Δ ⊢ φ ⇒ ξ ⇒ ψ
  S2 = dt2 φ,Δ⊢ξ⇒ψ

  S3 : Δ ⊢ (φ ⇒ ξ) ⇒ φ ⇒ ψ
  S3 = MP A2 S2

  SS : Δ ⊢ φ ⇒ ψ
  SS = MP S3 S1
```

We inductively extend the deduction theorem to finite sequences of assumptions.

```
deductionTheorem : ∀ Δ φ → ε ⊢ Δ Imply φ → Δ ⊢ φ
deductionTheorem ε φ ε⊢ΔImplyφ = ε⊢ΔImplyφ
deductionTheorem (ψ ∷ Δ) φ ε⊢ΔImply[ψ⇒φ] with deductionTheorem Δ (ψ ⇒ φ) ε⊢ΔImply[ψ⇒φ]
... | ind = dt1 ind
```

## Example theorems

```
-- ex falso
B1 : ∀ Δ φ → Δ ⊢ ⊥ ⇒ φ
B1 Δ φ = Δ⊢⊥⇒φ where

  Δ1 : Context
  Δ1 = ¬ φ ∷ ⊥ ∷ Δ
  Δ2 = ⊥ ∷ Δ
  
  Δ1⊢⊥ : Δ1 ⊢ ⊥
  Δ1⊢⊥ = Ass (there here)

  Δ2⊢¬¬φ : Δ2 ⊢ ¬ ¬ φ
  Δ2⊢¬¬φ = dt2 Δ1⊢⊥

  Δ2⊢φ : Δ2 ⊢ φ
  Δ2⊢φ = MP A3 Δ2⊢¬¬φ

  Δ⊢⊥⇒φ : Δ ⊢ ⊥ ⇒ φ
  Δ⊢⊥⇒φ = dt2 Δ2⊢φ
  
-- double negation
B2 : ∀ Δ φ  → Δ ⊢ ¬ φ ⇒ φ ⇒ ⊥
B2 Δ φ = dt2 (dt2 Γ₀⊢⊥)  where

   Γ₀ : Context
   Γ₀ = φ ∷ ¬ φ ∷ Δ

   Γ₀⊢φ : Γ₀ ⊢ φ
   Γ₀⊢φ = Ass here

   Γ₀⊢¬φ : Γ₀ ⊢ ¬ φ
   Γ₀⊢¬φ = Ass (there here)

   Γ₀⊢⊥ : Γ₀ ⊢ ⊥
   Γ₀⊢⊥ = MP Γ₀⊢¬φ Γ₀⊢φ
   
-- contradiction
-- used in the core lemma
B3 : ∀ Δ φ ψ → Δ ⊢ ¬ φ ⇒ φ ⇒ ψ
B3 Δ φ ψ = Δ⊢¬φ⇒φ⇒ψ where

  Γ₀ : Context
  Γ₀ = φ ∷ ¬ φ ∷ Δ

  Γ₀⊢⊥ : Γ₀ ⊢ ⊥
  Γ₀⊢⊥ = dt1 (dt1 (B2 Δ φ))

  Γ₀⊢ψ : Γ₀ ⊢ ψ
  Γ₀⊢ψ = MP (B1 Γ₀ ψ) Γ₀⊢⊥

  Δ⊢¬φ⇒φ⇒ψ : Δ ⊢ ¬ φ ⇒ φ ⇒ ψ
  Δ⊢¬φ⇒φ⇒ψ = dt2 (dt2 Γ₀⊢ψ)

-- proof by cases
-- useed in the second core lemma
B4 : ∀ Δ φ ψ → Δ ⊢ (φ ⇒ ψ) ⇒ (¬ φ ⇒ ψ) ⇒ ψ
B4 Δ φ ψ = dt2 (dt2 Δ1⊢ψ) where

  Δ1 Δ2 Δ3 : Context
  Δ1 = ¬ φ ⇒ ψ ∷ φ ⇒ ψ ∷ Δ
  Δ2 = ¬ ψ ∷ Δ1
  Δ3 = φ ∷ Δ2

  Δ3⊢φ : Δ3 ⊢ φ
  Δ3⊢φ = Ass here
  
  Δ3⊢φ⇒ψ : Δ3 ⊢ φ ⇒ ψ
  Δ3⊢φ⇒ψ = Ass (there (there (there here)))

  Δ3⊢ψ : Δ3 ⊢ ψ
  Δ3⊢ψ = MP Δ3⊢φ⇒ψ Δ3⊢φ
  
  Δ3⊢¬ψ : Δ3 ⊢ ¬ ψ
  Δ3⊢¬ψ = Ass (there here)
  
  Δ3⊢⊥ : Δ3 ⊢ ⊥
  Δ3⊢⊥ = MP Δ3⊢¬ψ Δ3⊢ψ

  Δ2⊢¬φ : Δ2 ⊢ ¬ φ
  Δ2⊢¬φ = dt2 Δ3⊢⊥

  Δ2⊢¬φ⇒ψ : Δ2 ⊢ ¬ φ ⇒ ψ
  Δ2⊢¬φ⇒ψ = Ass (there here)

  Δ2⊢ψ : Δ2 ⊢ ψ
  Δ2⊢ψ = MP Δ2⊢¬φ⇒ψ Δ2⊢¬φ

  Δ2⊢¬ψ : Δ2 ⊢ ¬ ψ
  Δ2⊢¬ψ = Ass here
  
  Δ2⊢⊥ : Δ2 ⊢ ⊥
  Δ2⊢⊥ = MP Δ2⊢¬ψ Δ2⊢ψ

  Δ1⊢¬¬ψ : Δ1 ⊢ ¬ ¬ ψ
  Δ1⊢¬¬ψ = dt2 Δ2⊢⊥

  Δ1⊢ψ : Δ1 ⊢ ψ
  Δ1⊢ψ = MP A3 Δ1⊢¬¬ψ

-- used in the core lemma
B5 : ∀ Δ φ ψ → Δ ⊢ φ ⇒ ¬ ψ ⇒ ¬ (φ ⇒ ψ)
B5 Δ φ ψ = dt2 (dt2 (dt2 Δ1⊢⊥)) where

  Δ1 : Context
  Δ1 = φ ⇒ ψ ∷ ¬ ψ ∷ φ ∷ Δ

  Δ1⊢φ : Δ1 ⊢ φ
  Δ1⊢φ = Ass (there (there here))

  Δ1⊢φ⇒ψ : Δ1 ⊢ φ ⇒ ψ
  Δ1⊢φ⇒ψ = Ass here

  Δ1⊢ψ : Δ1 ⊢ ψ
  Δ1⊢ψ = MP Δ1⊢φ⇒ψ Δ1⊢φ

  Δ1⊢¬ψ : Δ1 ⊢ ¬ ψ
  Δ1⊢¬ψ = Ass (there here)
  
  Δ1⊢⊥ : Δ1 ⊢ ⊥
  Δ1⊢⊥ = MP Δ1⊢¬ψ Δ1⊢ψ
```

## Soundness

```
soundness : ∀ Δ φ → Δ ⊢ φ → Δ ⊨ φ

soundness Δ φ (Ass ψ∈Δ) ϱ ⟦Δ⟧ = ⟦Δ⟧ ψ∈Δ

soundness Δ (φ ⇒ ψ ⇒ φ) A1 ϱ _ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
... | tt | ff = refl
... | ff | tt = refl
... | ff | ff = refl

soundness Δ ((φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ φ ⇒ ξ) A2 ϱ _ with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ | ⟦ ξ ⟧ ϱ
... | tt | tt | tt = refl
... | tt | tt | ff = refl
... | tt | ff | tt = refl
... | tt | ff | ff = refl
... | ff | tt | tt = refl
... | ff | tt | ff = refl
... | ff | ff | tt = refl
... | ff | ff | ff = refl

soundness Δ (((φ ⇒ ⊥) ⇒ ⊥) ⇒ φ) A3 ϱ _ with ⟦ φ ⟧ ϱ
-- soundness Δ (¬ ¬ φ ⇒ φ) A3 ϱ _ with ⟦ φ ⟧ ϱ
... | tt = refl
... | ff = refl

-- strong soundness of modus ponens
soundness Δ ψ (MP {φ = φ} Δ⊢φ⇒ψ Δ⊢φ) ϱ ⟦Δ⟧ with soundness _ _ Δ⊢φ⇒ψ ϱ ⟦Δ⟧ | soundness _ _ Δ⊢φ ϱ ⟦Δ⟧
... | ⟦φ⇒ψ⟧ϱ≡tt | ⟦φ⟧ϱ≡tt with ⟦ φ ⟧ ϱ | ⟦ ψ ⟧ ϱ
... | tt | tt = refl
```

## Completeness {#Completeness}

```
infix 51 _^_ _^^_

_^_ : Formula → Val → Formula
φ ^ ϱ = Cond𝔹 φ (φ ⇒ ⊥) (⟦ φ ⟧ ϱ)

_^^_ : Context → Val → Context
φs ^^ ϱ = map (λ φ → φ ^ ϱ) φs

-- list of all variables
vars : Context
vars = map `_ propNames
```

### Core lemma

```
core-lemma : ∀ φ (_ : Formula[⇒,⊥] φ) (ϱ : Val) →
  ------------------
  vars ^^ ϱ  ⊢ φ ^ ϱ
  
core-lemma .⊥ ⊥ ϱ = B0
core-lemma .(` p) (` p) ϱ = Ass p^ϱ∈ass where

  p∈ps : p ∈ propNames
  p∈ps = findPropName p

  `p∈vars : ` p ∈ vars
  `p∈vars =  map-∈ `_ {enumFin _} p∈ps

  p^ϱ∈ass : ` p ^ ϱ ∈ (vars ^^ ϱ)
  p^ϱ∈ass = map-∈ (λ x → x ^ ϱ) {vars} `p∈vars

core-lemma (φ ⇒ ψ) (viewφ ⇒ viewψ) ϱ
  with core-lemma ψ viewψ ϱ | inspect (⟦ ψ ⟧ ϱ)
... | indψ | it tt ⟦ψ⟧ϱ≡tt
  rewrite ⟦ψ⟧ϱ≡tt |
          ⇒𝔹-rewrite-tt-right (⟦ φ ⟧ ϱ) = MP A1 indψ 
... | indψ | it ff ⟦ψ⟧ϱ≡ff rewrite ⟦ψ⟧ϱ≡ff
  with core-lemma φ viewφ ϱ | inspect (⟦ φ ⟧ ϱ)
... | indφ | it tt ⟦φ⟧ϱ≡tt rewrite ⟦φ⟧ϱ≡tt = MP (MP (B5 _ _ _) indφ) indψ
... | indφ | it ff ⟦φ⟧ϱ≡ff rewrite ⟦φ⟧ϱ≡ff = MP (B3 _ _ _) indφ
```

-- B5 : ∀ {n} Δ (φ ψ : Formula n) → Δ ⊢ φ ⇒ ¬ ψ ⇒ ¬ (φ ⇒ ψ)

### Core lemma 2

```
core-lemma2 :
  Formula[⇒,⊥] φ →
  ε ⊨ φ →
  ∀ m ϱ →
  m ≤ n →
  --------------------
  drop m vars ^^ ϱ ⊢ φ

core-lemma2 {φ} viewφ ⊨φ 0 ϱ _ = repl fromCoreLemma (cong (λ C → vars ^^ ϱ ⊢ C) φ^ϱ≡φ) where

  fromCoreLemma : vars ^^ ϱ ⊢ φ ^ ϱ
  fromCoreLemma = core-lemma φ viewφ ϱ

  ⟦φ⟧ϱ≡tt : ⟦ φ ⟧ ϱ ≡ tt
  ⟦φ⟧ϱ≡tt = ⊨φ ϱ λ ()
  
  φ^ϱ≡φ : φ ^ ϱ ≡ φ
  φ^ϱ≡φ rewrite ⟦φ⟧ϱ≡tt = refl

core-lemma2 {φ} viewφ ⊨φ (suc m) ϱ sucm≤sucn
  with core-lemma2 {φ} viewφ ⊨φ m
... | ind = goal where

  distinct-ps : distinct propNames
  distinct-ps = enumFinDistinct _

  eql : length propNames ≡ n
  eql = enumFinLen n

  lenps>m : length propNames > m
  lenps>m rewrite eql = sucm≤sucn
                       
  v : PropName
  v = get-ne m propNames lenps>m

  v∈ps : v ∈ propNames ! m
  v∈ps = get-ne-∈! _ _ _
  
  ϱtt ϱff : Val
  ϱtt = ϱ [ v ↦ tt ]
  ϱff = ϱ [ v ↦ ff ]

  indtt : drop m vars ^^ ϱtt ⊢ φ
  indtt = ind ϱtt (trans-≤ n≤sucn sucm≤sucn)

  indff : drop m vars ^^ ϱff ⊢ φ
  indff = ind ϱff (trans-≤ n≤sucn sucm≤sucn)

  ϱttv≡tt : ϱtt v ≡ tt
  ϱttv≡tt = update-≡ v

  v^ϱtt≡v : ` v ^ ϱtt ≡ ` v
  v^ϱtt≡v rewrite ϱttv≡tt = refl

  ϱffv≡ff : ϱff v ≡ ff
  ϱffv≡ff = update-≡ v

  v^ϱff≡¬v : ` v ^ ϱff ≡ ¬ (` v)
  v^ϱff≡¬v rewrite ϱffv≡ff = refl

  drops : drop m propNames ≡ v ∷ drop (suc m) propNames
  drops = drop-cons m propNames lenps>m

  agree : ∀ b → map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agree b = map-Agree _ _ _ agree2 where

    agree2 : Agree (λ p → ` p ^ (ϱ [ v ↦ b ])) (λ p → ` p ^ ϱ) (drop (suc m) propNames)
    agree2 = Agree2-∘ (λ p → Cond𝔹 (` p) (¬ (` p))) (ϱ [ v ↦ b ]) ϱ (drop (suc m) propNames) agree1 where

     agree1 : Agree (ϱ [ v ↦ b ]) ϱ (drop (suc m) propNames)
     agree1 {p} p∈dropps = update-≢ v≢p where

       have : ∃[ k ] p ∈ drop (suc m) propNames ! k
       have = ∈→∈! _ _ p∈dropps

       k : ℕ
       k = dfst have

       p∈dropps!k : p ∈ drop (suc m) propNames ! k
       p∈dropps!k = dsnd have

       p∈ps : p ∈ propNames ! (suc m + k)
       p∈ps = drop-∈! p (suc m) _ _ p∈dropps!k

       v≢p : v ≢ p
       v≢p with v ≡? p
       ... | no proof = proof

       -- derive a contradiction
       ... | yes refl with distinct-ps m (suc m + k) v v∈ps p∈ps
       ... | impossible = F-elim (diseq impossible) where

         ineq : m < suc (m + k)
         ineq =  begin<
           m <≤⟨ n<sucn ⟩
           suc m
             ≤⟨ cong-≤ (Suc □) m≤m+k ⟩
           suc (m + k)
           ∎≤ where

             m≤m+k : m ≤ m + k
             m≤m+k = ≤+

         diseq : m ≢ suc (m + k)
         diseq = <→≢ ineq

  agreett : map (λ p → ` p ^ ϱtt) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agreett = agree tt

  agreeff : map (λ p → ` p ^ ϱff) (drop (suc m) propNames) ≡ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
  agreeff = agree ff

  equality : ∀ b → drop m vars ^^ (ϱ [ v ↦ b ]) ≡ Cond𝔹 (` v) (¬ (` v)) b ∷ drop (suc m) vars ^^ ϱ
  equality b = begin
    drop m vars ^^ (ϱ [ v ↦ b ])
      ≡⟨ cong (λ C → C ^^ (ϱ [ v ↦ b ])) (drop-map _ m propNames) ⟩
    map `_ (drop m propNames) ^^ (ϱ [ v ↦ b ])
      ≡⟨ map-∘ _ _ (drop m propNames) ⟩
    map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop m propNames)
      ≡⟨ cong (map λ p → ` p ^ (ϱ [ v ↦ b ])) drops ⟩
    map (λ p → ` p ^ (ϱ [ v ↦ b ])) (v ∷ drop (suc m) propNames)
      ≡⟨⟩
    (` v ^ (ϱ [ v ↦ b ])) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨⟩
    Cond𝔹 (` v) (¬ (` v)) (⟦ ` v ⟧ (ϱ [ v ↦ b ])) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨⟩
    Cond𝔹 (` v) (¬ (` v)) ((ϱ [ v ↦ b ]) v) ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨ cong (λ C → Cond𝔹 (` v) (¬ (` v)) C ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)) (update-≡ v)  ⟩
    ψ₀ ∷ map (λ p → ` p ^ (ϱ [ v ↦ b ])) (drop (suc m) propNames)
      ≡⟨ cong (λ C → ψ₀ ∷ C) (agree b) ⟩
    ψ₀ ∷ map (λ p → ` p ^ ϱ) (drop (suc m) propNames)
      ≡⟨ cong (λ C → ψ₀ ∷ C) (sym (map-∘ _ _ (drop (suc m) propNames)))  ⟩
    ψ₀ ∷ map `_ (drop (suc m) propNames) ^^ ϱ
      ≡⟨ cong (λ C → ψ₀ ∷ C ^^ ϱ) (sym (drop-map _ (suc m) propNames)) ⟩
    ψ₀ ∷ drop (suc m) vars ^^ ϱ ∎ where

      ψ₀ : Formula
      ψ₀ = Cond𝔹 (` v) (¬ (` v)) b

  eql-tt : drop m vars ^^ ϱtt ≡ ` v ∷ drop (suc m) vars ^^ ϱ
  eql-tt = equality tt

  eql-ff : drop m vars ^^ ϱff ≡ (¬ (` v)) ∷ drop (suc m) vars ^^ ϱ
  eql-ff = equality ff

  indtt' : drop (suc m) vars ^^ ϱ · ` v ⊢ φ
  indtt' = repl indtt (cong (λ C → C ⊢ φ) eql-tt)

  indff' : ¬ ` v ∷ drop (suc m) vars ^^ ϱ ⊢ φ
  indff' = repl indff (cong (λ C → C ⊢ φ) eql-ff)

  indtt'' : drop (suc m) vars ^^ ϱ ⊢ ` v ⇒ φ
  indtt'' = dt2 indtt'

  indff'' : drop (suc m) vars ^^ ϱ ⊢ ¬ (` v) ⇒ φ
  indff'' = dt2 indff' 

  goal : drop (suc m) vars ^^ ϱ ⊢ φ
  goal = MP (MP (B4 _ _ _) indtt'') indff''
```

### Weak completeness

```
weak-completeness : ∀ φ → Formula[⇒,⊥] φ → ε ⊨ φ → ε ⊢ φ
weak-completeness φ viewφ ⊨φ = ε⊢φ where

  anyVal : Val
  anyVal = λ _ → tt

  have : drop n vars ^^ anyVal ⊢ φ
  have = core-lemma2 viewφ ⊨φ n anyVal refl-≤

  vars-len : length vars ≡ n
  vars-len = begin
     length vars ≡⟨⟩
     length {A = Formula} (map `_ (enumFin _)) ≡⟨ map-length `_ (enumFin _) ⟩
     length (enumFin _) ≡⟨ enumFinLen n ⟩
     n ∎

  eql : drop n vars ≡ ε
  eql = begin
    drop n vars ≡⟨ cong (λ C → drop C vars) (sym vars-len) ⟩
    drop (length vars) vars ≡⟨ drop-all vars ⟩
    ε ∎

  eql1 : drop n vars ^^ anyVal ≡ ε
  eql1 = begin
     drop n vars ^^ anyVal
       ≡⟨ cong (λ C → C ^^ anyVal) eql  ⟩
     ε ^^ anyVal
       ≡⟨⟩
     ε ∎
  
  ε⊢φ : ε ⊢ φ
  ε⊢φ = repl have (cong (λ C → C ⊢ φ) eql1)
  
```

### Strong completeness

```
completeness : ∀ φ Δ → Formula[⇒,⊥] φ → All Formula[⇒,⊥] Δ → Δ ⊨ φ → Δ ⊢ φ
completeness φ Δ viewφ viewΔ = begin→
  Δ ⊨ φ
    →⟨ longSemDT1 Δ φ ⟩
  ε ⊨ Δ Imply φ
    →⟨ weak-completeness (Δ Imply φ) (view Δ φ viewφ viewΔ) ⟩
  ε ⊢ Δ Imply φ
    →⟨ deductionTheorem Δ φ ⟩
  Δ ⊢ φ
  ∎→  where

  view : ∀ Δ φ → Formula[⇒,⊥] φ → All Formula[⇒,⊥] Δ → Formula[⇒,⊥] (Δ Imply φ)
  view ε φ viewφ viewΔ = viewφ
  view (ψ ∷ Δ) φ viewφ viewΔ = view Δ (ψ ⇒ φ) (viewψ ⇒ viewφ) (viewΔ ∘ there) where

    viewψ : Formula[⇒,⊥] ψ
    viewψ = viewΔ here
```
