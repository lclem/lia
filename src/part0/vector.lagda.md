---
title: Vectors
---

```
{-# OPTIONS --allow-unsolved-metas #-}

module part0.vector where
open import part0.list
open import part0.logic
open import part0.depeq
open import part0.nat
open import part0.utils
open import part0.Fin
open import part0.fun
open import part0.decidable

data Vector {ℓ} (A : Set ℓ) : ℕ → Set ℓ where
  ε : Vector A zero
  _∷_ : ∀ {n} → A → Vector A n → Vector A (suc n)

-- dependent equality of two vectors of equal length:
-- _≡v[_]_ : ∀ {ℓ m n} {A : Set ℓ} → Vector A m → m ≡ n → Vector A n → Set ℓ
-- xs ≡v[ refl ] ys = xs ≡ ys

-- cons-≡v : ∀ {ℓ m n} {A : Set ℓ} {as : Vector A m} {bs : Vector A n} {a : A} →
--   (m≡n : m ≡ n) →
--   as ≡[ m≡n ] bs →
--   (a ∷ as) ≡[ cong suc m≡n ] (a ∷ bs)
-- cons-≡v refl refl = refl

-- convenient tuple-like notation
<_> : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → longAnd A n → Vector A n
<_> {n = 0} tt = ε
<_> {n = 1} a = a ∷ < tt >
<_> {n = suc (suc n)} (a , as) = a ∷ < as >

vsingleton : ∀ {ℓ} {A : Set ℓ} → A → Vector A 1
vsingleton a = < a >

infixr 26 _++v_
_++v_ : ∀ {ℓ} {m n} {A : Set ℓ} → Vector A m → Vector A n → Vector A (m + n)
ε ++v bs = bs
(a ∷ as) ++v bs = a ∷ (as ++v bs)

vmap : ∀ {ℓ m} {n} {A : Set ℓ} {B : Set m} → (A → B) → Vector A n → Vector B n
vmap _ ε = ε
vmap f (a ∷ as) = f a ∷ vmap f as

vmap-id : ∀ {ℓ} {n} {A : Set ℓ} {as : Vector A n} → vmap id as ≡ as
vmap-id {as = ε} = refl
vmap-id {as = a ∷ as} = cong (_∷_ a) vmap-id

vmap-∘ : ∀ {ℓ m o} {n} {A : Set ℓ} {B : Set m} {C : Set o} →
  {f : A → B} →
  {g : B → C} →
  {as : Vector A n} →
  vmap g (vmap f as) ≡ vmap (g ∘ f) as
vmap-∘ {as = ε} = refl
vmap-∘ {f = f} {g} {a ∷ as} with vmap-∘ {as = as}
... | eq = cong (λ as → g (f a) ∷ as) eq

-- vmap-∘-auto : ∀ {ℓ m o} {n} {A : Set ℓ} {B : Set m} {C : Set o}
--   {f : A → B}
--   {g : B → C} →
--   (as : Vector A n) →
--   vmap g (vmap f as) ≡ vmap (g ∘ f) as
-- vmap-∘-auto {f = f} {g = g} as = vmap-∘ {as = as}

vmap' : ∀ {ℓ m} {n} {A : Set ℓ} {B : Set m} → (A → ℕ → B) → Vector A n → Vector B n
vmap' f as = go f as zero where
    go : ∀ {ℓ m} {n} {A : Set ℓ} {B : Set m} → (A → ℕ → B) → Vector A n → ℕ → Vector B n
    go _ ε _ = ε
    go f (a ∷ as) n = f a n ∷ go f as (suc n)

vlength : ∀ {ℓ} {n} {A : Set ℓ} → Vector A n → ℕ
vlength {_} {n} _ = n

vzipWith : ∀ {ℓ m o} {n} {A : Set ℓ} {B : Set m} {C : Set o} → (A → B → C) → Vector A n → Vector B n → Vector C n
vzipWith _ ε ε = ε
vzipWith f (a ∷ as) (b ∷ bs) = f a b ∷ vzipWith f as bs

vmap-zipWith : ∀ {ℓA ℓB ℓC ℓD} {n} {A : Set ℓA} {B : Set ℓB} {C : Set ℓC} {D : Set ℓD} →
  (f : A → B) →
  (g : A → C) →
  (h : B → C → D) →
  (as : Vector A n) →
  vmap (λ x → h (f x) (g x)) as ≡ vzipWith h (vmap f as) (vmap g as)
vmap-zipWith _ _ _ ε = refl
vmap-zipWith f g h (a ∷ as) with vmap-zipWith f g h as
... | p = cong2 _∷_ refl p

vfoldl : ∀ {ℓ m} {n} {A : Set ℓ} {B : Set m} → (B → A → B) → B → Vector A n → B
vfoldl f b ε = b
vfoldl f b (a ∷ as) = vfoldl f (f b a) as

vconcat : ∀ {ℓ} {m n} {A : Set ℓ} → Vector (Vector A m) n → Vector A (n * m)
-- cannot use "vfoldl _++v_ ε" since the type of _++v_ changes at every step
-- (could use TVectors though...
vconcat ε = ε
vconcat (as ∷ ass) = as ++v vconcat ass

-- essentially vfoldl1 _∧_
vand : ∀ {ℓ n} → Vector (Set ℓ) n → Set ℓ
vand ε = ⊤
vand (A ∷ ε) = A
vand (A ∷ As) = A ∧ vand As

vtake : ∀ {ℓ} {A : Set ℓ} (m : ℕ) {n : ℕ} → Vector A (m + n) → Vector A m
vtake zero _ = ε
vtake (suc k) (a ∷ as) = a ∷ vtake k as

-- alternative definition
-- vtake : ∀ {ℓ n} {A : Set ℓ} → (k : Fin n) → Vector A n → Vector A (Fin2ℕ k)
-- vtake fzero _ = ε
-- vtake (fsuc k) (a ∷ as) = a ∷ vtake k as

vdrop : ∀ {ℓ} {A : Set ℓ} (m : ℕ) {n : ℕ} → Vector A (m + n) → Vector A n
vdrop zero as = as
vdrop (suc m) (_ ∷ as) = vdrop m as

vtake-drop-++ : ∀ {ℓ} {A : Set ℓ} (m : ℕ) {n : ℕ} (as : Vector A (m + n)) → vtake m as ++v vdrop m as ≡ as
vtake-drop-++ zero _ = refl
vtake-drop-++ (suc m) (a ∷ as) with vtake-drop-++ m as
... | ind = cong (_∷_ a) ind

l2v : ∀ {ℓ} {A : Set ℓ} → (as : A *) → Vector A (length as)
l2v ε = ε
l2v (a ∷ as) = a ∷ l2v as

v2l : ∀ {ℓ} {n} {A : Set ℓ} → Vector A n → A *
v2l ε = ε
v2l (a ∷ as) = a ∷ v2l as

v2l-length : ∀ {ℓ} {n} {A : Set ℓ} → (as : Vector A n) → length (v2l as) ≡ n
v2l-length ε = refl
v2l-length (_ ∷ as) with v2l-length as
... | ind = cong suc ind

-- problem: n != length (v2l as)
-- solution: we use dependent equality of two vectors of provably equal length!
l2v-v2l-id : ∀ {ℓ} {n} {A : Set ℓ} → (as : Vector A n) → l2v (v2l as) ≡[ v2l-length as ] as
l2v-v2l-id ε = refl
l2v-v2l-id {A = A} (a ∷ as) with v2l-length as | l2v-v2l-id as
-- we need to call v2l-length for the dependent equality to go through
-- new it takes forever to check
... | p | ind = dcong'' {A = Vector A} suc (_∷_ a) p ind

v2l-l2v-id : ∀ {ℓ} {A : Set ℓ} → (as : A *) → v2l (l2v as) ≡ as
v2l-l2v-id as = {! as  !}

-- [_] : ∀ {ℓ} {A : Set ℓ} {n : ℕ} → longAnd A n → A *
-- [ as ] = v2l (< as >)
--
-- singleton : ∀ {ℓ} {A : Set ℓ} → A → A *
-- singleton a = [ a ]

concat-vconcat : ∀ {ℓ} {m n} {A : Set ℓ} →
  (ass : Vector (Vector A m) n) →
  concat (v2l $ vmap v2l ass) ≡ v2l (vconcat ass)
concat-vconcat = {!   !}

concat-vconcat1 : ∀ {ℓ} {n} {A : Set ℓ} →
  (ass : Vector (A *) n) →
  concat (v2l ass) ≡ vfoldl _++_ ε ass
concat-vconcat1 = {!   !}

-- this direction cannot be stated, need TList (?) ...
-- vconcat-concat : ∀ {ℓ} {A : Set ℓ} →
--   (ass : A * *) →
--   vconcat (l2v $ map l2v ass) ≡ l2v (concat ass)
-- vconcat-concat = {!   !}

-- infixl 9 _!_  -- _[!]_
-- _!_ : {n : ℕ} {A : Set} → Vector A n → Fin n → A
-- ε ! ()
-- x ∷ xs ! fzero  = x
-- x ∷ xs ! fsuc i = xs ! i

-- if needed, replace "!" with "at"
-- infix 5 _∈v_at_
-- data _∈v_at_ {ℓ} {A : Set ℓ} : ∀ {n} → A → Vector A n → Fin n → Set ℓ where
--     here : ∀ {x} {n} {xs : Vector A n} → x ∈v (x ∷ xs) at fzero
--     there : ∀ {x y} {n k} {xs : Vector A n} → x ∈v xs at k → x ∈v (y ∷ xs) at (fsuc k)

infix 5 _∈v_
data _∈v_ {ℓ} {A : Set ℓ} : ∀ {n} → A → Vector A n → Set ℓ where
    here : ∀ {x} {n} {xs : Vector A n} → x ∈v (x ∷ xs)
    there : ∀ {x y} {n} {xs : Vector A n} → x ∈v xs → x ∈v (y ∷ xs)

infix 5 _∈v_at_
data _∈v_at_ {ℓ} {A : Set ℓ} : ∀ {n} → A → Vector A n → Fin n → Set ℓ where
    here : ∀ {x} {n} {xs : Vector A n} → x ∈v (x ∷ xs) at fzero
    there : ∀ {x y} {n} {k} {xs : Vector A n} → x ∈v xs at k → x ∈v (y ∷ xs) at (fsuc k)

getIndex : ∀ {ℓ n} {A : Set ℓ} {a : A} {as : Vector A n} → a ∈v as → ∃[ k ] a ∈v as at k
getIndex here = fzero , here
getIndex (there a∈vas) with getIndex a∈vas
... | (k , a∈vasatk) = fsuc k , there a∈vasatk

forgetIndex : ∀ {ℓ n} {A : Set ℓ} {a : A} {as : Vector A n} {k} → a ∈v as at k → a ∈v as
forgetIndex = {!   !}

_¬∈v_ : ∀ {ℓ} {A : Set ℓ} {n} → A → Vector A n → Set ℓ
a ¬∈v as = ¬(a ∈v as)

vfind : ∀ {ℓ n} {A : Set ℓ} → (a : A) → (as : Vector A n) → (∃[ i ] a ∈v as at i) ∨ a ¬∈v as
vfind = {!   !}

-- by induction on the membership evidence
∈v-++1 : ∀ {ℓ m n} {A : Set ℓ} {a : A} {i : Fin m} {as : Vector A m} {bs : Vector A n} →
  a ∈v as at i →
  a ∈v (as ++v bs) at (Fin-monotone ≤+ i)
∈v-++1 here = here
∈v-++1 (there a∈as!i) with ∈v-++1 a∈as!i
... | a∈as++bs!i = there a∈as++bs!i

-- by induction on the vector as
∈v-++2 : ∀ {ℓ m n} {A : Set ℓ} {a : A} {i : Fin n} {as : Vector A m} {bs : Vector A n} →
  a ∈v bs at i →
  a ∈v (as ++v bs) at (fadd m i)
∈v-++2 {as = ε} a∈bs!i = a∈bs!i
∈v-++2 {as = _ ∷ as} a∈bs!i with ∈v-++2 {as = as} a∈bs!i
... | a∈as++bs!faddni = there a∈as++bs!faddni

--
-- j : Fin n
-- j = dfst q
--
-- j' : Fin (m + n)
-- j' = fadd m j

-- it could be improved to return a non-membership proof in the Nothing case...
-- _∈v?_ : ∀ {ℓ} {A : Set ℓ} {n} {{_ : Eq A}} → (a : A) → (as : Vector A n) → Maybe (∃[ k ] a ∈v as ! k)
-- a ∈v? ε = Nothing
-- a ∈v? (b ∷ as) with a ≡? b
-- ... | yes {proof = refl} = Just (0 , here)
-- ... | no with a ∈v? as
-- ... | Nothing = Nothing
-- ... | Just (k , a∈vas!k) = Just (suc k , there a∈vas!k)

-- fetch : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {a : A} {n k} {as : Vector A n} → a ∈v as ! k → (bs : Vector B n) → ∃[ b ] b ∈v bs ! k
-- fetch here (b ∷ _) = b , here
-- fetch (there p) (_ ∷ bs) with fetch p bs
-- ... | b , q = b , there q

-- safe vector indexing
infix 11 _!_
_!_ : ∀ {ℓ} {A : Set ℓ} {n} → Vector A n → Fin n → A
(a ∷ _) ! fzero = a
(_ ∷ as) ! fsuc k = as ! k

membershipCorrect1 : ∀ {ℓ} {n} {A : Set ℓ} {i : Fin n} {as : Vector A n} {a : A} → a ∈v as at i → as ! i ≡ a
membershipCorrect1 here = refl
membershipCorrect1 (there memb) = membershipCorrect1 memb

membershipCorrect2 : ∀ {ℓ} {n} {A : Set ℓ} {i : Fin n} {as : Vector A n} → (as ! i) ∈v as at i
membershipCorrect2 = {!   !}

vmap-! : ∀ {ℓ m} {n} {A : Set ℓ} {B : Set m} →
  {f : A → B} →
  {k : Fin n} →
  (as : Vector A n) →
  vmap f as ! k ≡ f (as ! k)
vmap-! {k = fzero} (a ∷ as) = refl
vmap-! {k = fsuc k} (_ ∷ as) = vmap-! {k = k} as

∈v→∈ : ∀ {ℓ n} {A : Set ℓ} {a : A} {as : Vector A n} → a ∈v as → a ∈ v2l as
∈v→∈ = {!   !}

∈→∈v : ∀ {ℓ} {A : Set ℓ} {a : A} {as : A *} → a ∈ as → a ∈v l2v as
∈→∈v = {!   !}

∈→∈v-2 : ∀ {ℓ n} {A : Set ℓ} {a : A} {as : Vector A n} → a ∈ (v2l as) → a ∈v as
∈→∈v-2 = {!   !}

-- vector-list concat
vlconcat : ∀ {ℓ} {n} {A : Set ℓ} → Vector (A *) n → A *
vlconcat ε = ε
vlconcat (as ∷ ass) = as ++ vlconcat ass

vlconcat-vmap-singleton : ∀ {ℓ n} {A : Set ℓ} (xs : Vector A n) → vlconcat (vmap (λ x → [ x ]) xs) ≡ v2l xs
vlconcat-vmap-singleton = {!   !}

∉-vlconcat : ∀ {ℓ} {n} {A : Set ℓ} {a : A} {as : A *} {ass : Vector (A *) n} →
  a ∉ vlconcat ass →
  as ∈v ass →
  a ∉ as
∉-vlconcat p q = {!   !}

data DVector' {ℓ} (A : ℕ → Set ℓ) : ℕ → ℕ → Set ℓ where
  ε : ∀ {k} → DVector' A k zero
  _∷_ : ∀ {n k} → A k → DVector' A (suc k) n → DVector' A k (suc n)

DVector : ∀ {ℓ} → (ℕ → Set ℓ) → ℕ → Set ℓ
DVector A = DVector' A zero

dvmap : ∀ {n} {A B : ℕ → Set} → ((n : ℕ) → A n → B n) → DVector A n → DVector B n
dvmap f as = go f zero as where
     go : ∀ {n} {A B : ℕ → Set} → ((n : ℕ) → A n → B n) → (k : ℕ) → DVector' A k n → DVector' B k n
     go _ _ ε = ε
     go f n (a ∷ as) = f n a ∷ go f (suc n) as

-- v2dvec

-- each element in the vector has its own type
data TVector {ℓ} : {n : ℕ} → Vector (Set ℓ) n → Set ℓ where
    ε : TVector ε
    _∷_ : ∀ {n} {A : Set ℓ} {As : Vector (Set ℓ) n} → A → TVector As → TVector (A ∷ As)

ttypes : ∀ {ℓ} {n} {As : Vector (Set ℓ) n} → TVector As → Vector (Set ℓ) n
ttypes {As = As} _ = As

tlength : ∀ {ℓ} {n} {As : Vector (Set ℓ) n} → TVector As → ℕ
tlength {n = n} _ = n

_++t_ : ∀ {ℓ} {m n} {As : Vector (Set ℓ) m} {Bs : Vector (Set ℓ) n} →
  TVector As →
  TVector Bs →
  TVector (As ++v Bs)
_++t_ ε bs = bs
_++t_ (a ∷ as) bs = a ∷ _++t_ as bs

-- infix 5 _∈t_!_
-- data _∈t_!_ {ℓ} : ∀ {n} {As : Vector (Set ℓ) n} → A → TVector As n → ℕ → Set ℓ where
--     here : ∀ {x} {n} {xs : TVector As n} → x ∈t (x ∷ xs) ! zero
--     there : ∀ {x y} {n k} {xs : TVector As n} → x ∈t xs ! k → x ∈t (y ∷ xs) ! (suc k)

-- tfind : ∀ {ℓ} {n k} {A : Set ℓ} {As : Vector (Set ℓ) n} → A ∈v As ! k → TVector As → A
-- tfind here (a ∷ _) = a
-- tfind (there p) (_ ∷ as) = tfind p as

-- tfetch : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {a : A} {n k} {as : Vector A n} {Bs : Vector (Set m) n} →
--     a ∈v as ! k →
--     TVector Bs →
--     ∃[ B ] B ∈v Bs ! k ∧ B
-- tfetch {Bs = Bs} p bs with fetch p Bs
-- ... | B , q = B , q , tfind q bs

-- map a TVector of functions (each of different type) on a TVector of arguments
tmap : ∀ {ℓ} {n} {As Bs : Vector (Set ℓ) n} →
  TVector (vzipWith Fn As Bs) →
  TVector As →
  TVector Bs
tmap {_} .{zero} {ε} {ε} ε ε = ε
tmap {ℓ} {suc n} {A ∷ As} {B ∷ Bs} (f ∷ fs) (a ∷ as) = f a ∷ tmap fs as

-- map the same dependent function onto a Vector
tmap1 : ∀ {ℓ m} {n} {A : Set ℓ} {B : A → Set m} →
  (f : ((a : A) → B a)) →
  (as : Vector A n) →
  TVector (vmap B as)
tmap1 _ ε = ε
tmap1 f (a ∷ as) = f a ∷ tmap1 f as

-- map a Vector of dependent functions onto a Vector of arguments
tmap2 : ∀ {ℓ} {n} {A : Set ℓ} {B : A → Set ℓ} →
  Vector ((a : A) → B a) n →
  (as : Vector A n) →
  TVector (vmap B as)
tmap2 ε ε = ε
tmap2 (f ∷ fs) (a ∷ as) = f a ∷ tmap2 fs as

-- another useful variant
tmap3 : ∀ {ℓ m} {n}
  {A : Set ℓ}
  {B C : A → Set m} →
  (As : Vector A n) →
  TVector (vmap (λ a → (B a → C a)) As) →
  TVector (vmap B As) →
  TVector (vmap C As)
tmap3 ε _ _ = ε
tmap3 (_ ∷ as) (f ∷ fs) (b ∷ bs) = f b ∷ tmap3 as fs bs

-- mapping a dependent function over a Vector yields a TVector
vmapT : ∀ {ℓ m} {n} {A : Set ℓ} {B : A → Set m} →
  (as : Vector A n) →
  ((a : A) → B a) →
  TVector (vmap B as)
vmapT = {!   !}

vmap∈ : ∀ {ℓ m} {n} {A : Set ℓ} {B : A → Set m} →
  (as : Vector A n) →
  ((a : A) → a ∈v as → B a) →
  TVector (vmap B as)
vmap∈ = {!   !}
-- vmap∈ ε = ε
-- vmap∈ (a ∷ as) f = f a a∈as ∷ vmap∈ as f where

tzipWith : ∀ {ℓ m o} {n} {A : Set ℓ} {B : Set m} {C : A → B → Set o} →
    ((a : A) → (b : B) → C a b) →
    (as : Vector A n) → (bs : Vector B n) →
    TVector (vzipWith C as bs)
tzipWith _ ε ε = ε
tzipWith f (a ∷ as) (b ∷ bs) = f a b ∷ tzipWith f as bs

-- given a vector of equality proofs return an equality proof of vectors
vec≡ : ∀ {ℓ} {n} {A : Set ℓ} {as bs : Vector A n} → TVector (vzipWith _≡_ as bs) → as ≡ bs
vec≡ {as = ε} {bs = ε} ε = refl
vec≡ {as = a ∷ as} {bs = b ∷ bs} (p ∷ ps) with vec≡ ps
... | q = cong2 _∷_ p q

-- if two functions agree on a vector, then their vmaps are equal
vec≡1 : ∀ {ℓ m} {n} {A : Set ℓ} {B : Set m} {as : Vector A n} →
  (f g : A → B) →
  TVector (vmap (λ x → f x ≡ g x) as) →
  vmap f as ≡ vmap g as
vec≡1 {A = A} {B = B} {as = as} f g p with vmap-zipWith f g (_≡_) as
... | q = vec≡ $ subst TVector q p

-- combine vec≡1 and tmap1
vmap-≡ : ∀ {ℓ m} {n} {A : Set ℓ} {B : Set m} →
  (f g : A → B) →
  (f≡g : (a : A) → f a ≡ g a) →
  (as : Vector A n) →
  vmap f as ≡ vmap g as
vmap-≡ f g f≡g as = vec≡1 f g (tmap1 f≡g as)

vmap-≡-auto : ∀ {ℓ m} {n} {A : Set ℓ} {B : Set m}
  {f g : A → B} →
  (f≡g : (a : A) → f a ≡ g a) →
  (as : Vector A n) →
  vmap f as ≡ vmap g as
vmap-≡-auto {f = f} {g = g} = vmap-≡ f g

-- an equality principle for vectors
vec-≡-! : ∀ {ℓ} {n} {A : Set ℓ} {as bs : Vector A n} → ∀[ k ] as ! k ≡ bs ! k → as ≡ bs
vec-≡-! {as = ε} {ε} _ = refl
vec-≡-! {as = a ∷ as} {b ∷ bs} f with f fzero
... | refl with vec-≡-! {as = as} {bs} λ k → f (fsuc k)
... | refl = refl

-- Nice constructor for functions of many arguments
IFn : ∀ {ℓ} (A : Set ℓ) (n : ℕ) (B : Set ℓ) → Set ℓ
IFn _ zero B = B
IFn A (suc n) B = A → IFn A n B

vcurry : ∀ {ℓ} {n} {A : Set ℓ} {B : Set ℓ} → (Vector A n → B) → IFn A n B
vcurry {n = zero} f = f ε
vcurry {n = suc n} f a = vcurry {n = n} (λ as → f (a ∷ as))

vuncurry : ∀ {ℓ} {n} {A : Set ℓ} {B : Set ℓ} → IFn A n B → Vector A n → B
vuncurry b ε = b
vuncurry f (a ∷ as) = vuncurry (f a) as

-- fconst : ∀ {ℓ} {n} {A : Set ℓ} {B : Set ℓ} → B → IFn A n B
-- fconst b = vcurry (λ _ → b)

-- sequential vector valuation update
infixl 300 _v[_↦_]
_v[_↦_] vupdate : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {n} {{_ : Eq A}} → (A → B) → Vector A n → Vector B n → A → B
-- it should alternatively be defined by induction based on ρ [ x ↦ a ]
-- (ρ v[ xs ↦ as ]) y with y ∈v? xs
-- ... | Nothing = ρ y
-- ... | Just (k , y∈xs!k) = dfst $ fetch y∈xs!k as
ρ v[ ε ↦ ε ] = ρ
-- we need the last occurrence of a variable to be used for the substitution
ρ v[ x ∷ xs ↦ a ∷ as ] = ρ [ x ↦ a ] v[ xs ↦ as ]

vupdate ρ xs as = ρ v[ xs ↦ as ]

vupdate-++ : ∀ {ℓ m} {X : Set ℓ} {{_ : Eq X}} {A : Set m} {n k} {ρ : X → A} {xs : Vector X n} {ys : Vector X k} {as : Vector A n} {bs : Vector A k} →
  ρ v[ xs ++v ys ↦ as ++v bs ] ≡ ρ v[ xs ↦ as ] v[ ys ↦ bs ]
vupdate-++ {xs = ε} {as = ε} = refl
vupdate-++ {ρ = ρ} {xs = x ∷ xs} {as = a ∷ as} = vupdate-++ {ρ = ρ [ x ↦ a ]} {xs = xs} {as = as}

vupdate-¬∈v : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {{_ : Eq A}} (ρ : A → B) {a : A} {as : Vector A n} {bs : Vector B n} →
  a ¬∈v as →
  (ρ v[ as ↦ bs ]) a ≡ ρ a
vupdate-¬∈v ρ a¬∈as = {!   !}

-- express that all elements in a vector are distinct
vdistinct : ∀ {ℓ n} {A : Set ℓ} → Vector A n → Set ℓ
vdistinct as = ∀[ i ] ∀[ j ] ∀[ a ] (a ∈v as at i → a ∈v as at j → i ≡ j)

vrepetition : ∀ {ℓ n} {A : Set ℓ} → Vector A n → Set
vrepetition as = ∃[ i ] ∃[ j ] i ≢ j ∧ as ! i ≡ as ! j

distinct→¬repetition : ∀ {ℓ m} {A : Set ℓ} {as : Vector A m} → vdistinct as → ¬ vrepetition as
distinct→¬repetition {as = as} dist (i , j , i≢j , as!i≡as!j) = i≢j (dist i j (as ! i) membershipCorrect2 as!i∈vasatj ) where

  as!i∈vasatj : as ! i ∈v as at j
  as!i∈vasatj = repl membershipCorrect2 (cong (λ bs → bs ∈v as at j) (sym as!i≡as!j))

-- using decidability of equality on Fin
¬repetition→distinct : ∀ {ℓ m} {A : Set ℓ} {as : Vector A m} → ¬ vrepetition as → vdistinct as
¬repetition→distinct {as = as} ¬rep i j a a∈as!i a∈as!j with i ≡? j
... | yes {refl} = refl
... | no {i≢j} = ⊥-elim (¬rep rep) where

  rep : vrepetition as
  rep = i , j , i≢j , (begin
    as ! i
      ≡⟨ membershipCorrect1 a∈as!i ⟩
    a
      ≡⟨ sym (membershipCorrect1 a∈as!j) ⟩
    as ! j
    ∎)

vrepetition-++ : ∀ {ℓ m n} {A : Set ℓ} {as : Vector A m} {bs : Vector A n} {a : A} →
  a ∈v as →
  a ∈v bs →
  vrepetition (as ++v bs)
vrepetition-++ {m = m} {n} {as = as} {bs} {a} a∈as a∈bs = i' , j' , i'≢j' , eql where

  p : ∃[ i ] a ∈v as at i
  p = getIndex a∈as

  q : ∃[ j ] a ∈v bs at j
  q = getIndex a∈bs

  i : Fin m
  i = dfst p

  i' : Fin (m + n)
  i' = Fin-monotone ≤+ i

  j : Fin n
  j = dfst q

  j' : Fin (m + n)
  j' = fadd m j

  i'≢j' : i' ≢ j'
  i'≢j' = Fin-add-≢ i j

  ati : a ∈v (as ++v bs) at i'
  ati = ∈v-++1 (dsnd p)

  atj : a ∈v (as ++v bs) at j'
  atj = ∈v-++2 (dsnd q)

  eql : (as ++v bs) ! i' ≡ (as ++v bs) ! j'
  eql = begin
    (as ++v bs) ! i'
      ≡⟨ membershipCorrect1 ati ⟩
    a
      ≡⟨ sym (membershipCorrect1 atj) ⟩
    (as ++v bs) ! j'
    ∎

vdistinct-++ : ∀ {ℓ m n} {A : Set ℓ} {as : Vector A m} {bs : Vector A n} {a : A} →
  a ∈v as →
  vdistinct (as ++v bs) →
  a ¬∈v bs
vdistinct-++ a∈as dst a∈bs = distinct→¬repetition dst (vrepetition-++ a∈as a∈bs)

vdistinct-¬∈ : ∀ {ℓ n} {A : Set ℓ} {as : Vector A n} {a : A} →
  vdistinct as →
  a ¬∈v as →
  vdistinct (a ∷ as)
vdistinct-¬∈ = {!   !}

infixl 20 _⊆v_
_⊆v_ : ∀ {ℓ m n} {A : Set ℓ} {{_ : Eq A}} → Vector A m → Vector A n → Set ℓ
xs ⊆v ys = ∀[ x ] (x ∈v xs → x ∈v ys)

-- noncontiguous subword embedding
infixl 9 _⊑v_
data _⊑v_ {ℓ} {A : Set ℓ} : ∀ {m n} → Vector A m → Vector A n → Set where
  stop : ∀ {n} {bs : Vector A n} → ε ⊑v bs
  match : ∀ {m n} {a : A} {as : Vector A m} {bs : Vector A n} → as ⊑v bs → a ∷ as ⊑v a ∷ bs
  skip : ∀ {m n} {a : A} {as : Vector A m} {bs : Vector A n} → as ⊑v bs → as ⊑v a ∷ bs

refl-⊑v : ∀ {ℓ n} {A : Set ℓ} {as : Vector A n} → as ⊑v as
refl-⊑v = {!   !}

vtakeIs⊑ : ∀ {ℓ n} {A : Set ℓ} (m : ℕ) (as : Vector A (m + n)) → vtake m as ⊑v as
vtakeIs⊑ zero _ = stop
vtakeIs⊑ (suc m) (_ ∷ as) with vtakeIs⊑ m as
... | take⊑as = match take⊑as

vdropIs⊑ : ∀ {ℓ n} {A : Set ℓ} (m : ℕ) (as : Vector A (m + n)) → vdrop m as ⊑v as
vdropIs⊑ zero _ = refl-⊑v
vdropIs⊑ (suc m) (_ ∷ as) with vdropIs⊑ m as
... | drop⊑as = skip drop⊑as

⊑v-++-1 : ∀ {ℓ m n} {A : Set ℓ} (as : Vector A m) (bs : Vector A n) → as ⊑v as ++v bs
⊑v-++-1 = {!   !}

⊑v-++-2 : ∀ {ℓ m n} {A : Set ℓ} (as : Vector A m) (bs : Vector A n) → as ⊑v bs ++v as
⊑v-++-2 = {!   !}

infixl 9 _⊑v_atIndices_
data _⊑v_atIndices_ {ℓ} {A : Set ℓ} : ∀ {m n} → Vector A m → Vector A n → Vector (Fin n) m → Set where
  stop : ∀ {n} {bs : Vector A n} → ε ⊑v bs atIndices ε
  match : ∀ {m n} {a : A} {as : Vector A m} {bs : Vector A n} {is : Vector (Fin n) m} → as ⊑v bs atIndices is → a ∷ as ⊑v a ∷ bs atIndices (fzero ∷ vmap fsuc is)
  skip : ∀ {m n} {a : A} {as : Vector A m} {bs : Vector A n} {is : Vector (Fin n) m} → as ⊑v bs atIndices is → as ⊑v a ∷ bs atIndices (vmap fsuc is)

⊑v→⊆v : ∀ {ℓ m n} {A : Set ℓ} {{_ : Eq A}} {as : Vector A m} {bs : Vector A n} → as ⊑v bs → as ⊆v bs
⊑v→⊆v = {!   !}

⊆v→⊆ : ∀ {ℓ m n} {A : Set ℓ} {{_ : Eq A}} {as : Vector A m} {bs : Vector A n} → as ⊆v bs → v2l as ⊆ v2l bs
⊆v→⊆ = {!   !}

buildIndices : ∀ {ℓ} {A : Set ℓ} {m n} {as : Vector A m} {bs : Vector A n} →
  as ⊑v bs →
  ∃[ is ] as ⊑v bs atIndices is
buildIndices stop = ε , stop
buildIndices (match as⊑bs) with buildIndices as⊑bs
... | is , as⊑bsAtis = (fzero ∷ vmap fsuc is) , match as⊑bsAtis
buildIndices (skip as⊑bs) with buildIndices as⊑bs
... | is , as⊑bsAtis = vmap fsuc is , skip as⊑bsAtis

indicesDistinct : ∀ {ℓ m n} {A : Set ℓ} {as : Vector A m} {bs : Vector A n} {is : Vector (Fin n) m} {i j : Fin m} →
  as ⊑v bs atIndices is → i ≢ j → is ! i ≢ is ! j
indicesDistinct = {!   !}

indicesCorrect : ∀ {ℓ m n} {A : Set ℓ} {as : Vector A m} {bs : Vector A n} {is : Vector (Fin n) m} → as ⊑v bs atIndices is → ∀[ i ] bs ! (is ! i) ≡ as ! i
indicesCorrect = {!   !}

vrepetition-⊑ : ∀ {ℓ m n} {A : Set ℓ} (as : Vector A m) (bs : Vector A n) →
  as ⊑v bs →
  vrepetition as →
  vrepetition bs
vrepetition-⊑ as bs as⊑bs (i , j , i≢j , as!i≡as!j)
  with buildIndices as⊑bs
... | is , as⊑bsAtis = is ! i , is ! j , indicesDistinct as⊑bsAtis i≢j , goal where

  goal : bs ! (is ! i) ≡ bs ! (is ! j)
  goal = begin
    bs ! (is ! i)
      ≡⟨ indicesCorrect as⊑bsAtis i ⟩
    as ! i
      ≡⟨ as!i≡as!j ⟩
    as ! j
      ≡⟨ sym (indicesCorrect as⊑bsAtis j) ⟩
    bs ! (is ! j)
    ∎

vdistinct-⊑ : ∀ {ℓ m n} {A : Set ℓ} (as : Vector A m) (bs : Vector A n) →
  as ⊑v bs →
  vdistinct bs →
  vdistinct as
vdistinct-⊑ as bs as⊑bs = ¬repetition→distinct ∘ ¬→-Lemma2 (vrepetition-⊑ as bs as⊑bs) ∘ distinct→¬repetition

-- this only holds if k is the largest index s.t. as ! k occurs in as...
-- in particular, this holds if all the as are distinct...
vupdate-! : ∀ {ℓ m} {A : Set ℓ} {B : Set m} {n} {{_ : Eq A}} {ρ : A → B} {as : Vector A n} {bs : Vector B n} {k : Fin n} →
  vdistinct as →
  (ρ v[ as ↦ bs ]) (as ! k) ≡ bs ! k

vupdate-! {n = suc n} {ρ = ρ} {a ∷ as} {b ∷ bs} {fzero} p = begin
  (ρ [ a ↦ b ] v[ as ↦ bs ]) a
    ≡⟨ vupdate-¬∈v _ a¬∈vas ⟩
  (ρ [ a ↦ b ]) a
    ≡⟨ update-≡ a ⟩
  b
  ∎ where

  a¬∈vas : a ¬∈v as
  a¬∈vas a∈vas = fzero≢fsuc (p fzero (fsuc k) a here (there a∈vasatk)) where

    pp : ∃[ k ] a ∈v as at k
    pp = getIndex a∈vas

    k : Fin n
    k = dfst pp

    a∈vasatk : a ∈v as at k
    a∈vasatk = dsnd pp

vupdate-! {ρ = ρ} {a ∷ as} {b ∷ bs} {fsuc k} p = vupdate-! {ρ = ρ [ a ↦ b ]} {as} {bs} {k} q where

  q : ∀[ i ] ∀[ j ] ∀[ a ] (a ∈v as at i → a ∈v as at j → i ≡ j)
  q i j a a∈vasati a∈vasatj = inj-fsuc (p (fsuc i) (fsuc j) a (there a∈vasati) (there a∈vasatj))

-- inclusion of vectors (up to permutation)
-- infixl 20 _⊆_
-- _⊆_ : ∀ {ℓ} {A : Set ℓ} {m n} → {{Eq A}} → Vector A m → Vector A n → Set ℓ
-- xs ⊆ ys = ∀[ x ] (x ∈v xs → x ∈v ys)

vdisjoint : ∀ {ℓ m n} {A : Set ℓ} {{_ : Eq A}} → Vector A m → Vector A n → Set ℓ
vdisjoint as bs = ∀[ a ] (a ∈v as → a ¬∈v bs)

vupdate-flip : ∀ {ℓ m n o} {A : Set ℓ} {B : Set m} {{_ : Eq A}} (ρ : A → B) {as : Vector A n} {bs : Vector B n} {cs : Vector A o} {ds : Vector B o} →
  vdisjoint as cs →
  ρ v[ as ↦ bs ] v[ cs ↦ ds ] ≡ ρ v[ cs ↦ ds ] v[ as ↦ bs ]
vupdate-flip = {!   !}

vupdate-swap : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {{_ : Eq A}} (ρ : A → B) {as : Vector A n} {bs : Vector B n} {a : A} {b : B} →
  a ¬∈v as →
  ρ v[ as ↦ bs ] [ a ↦ b ] ≡ ρ [ a ↦ b ] v[ as ↦ bs ]
vupdate-swap = {!   !}

-- prove it using vupdate-! above
vupdate-∈at : ∀ {ℓ m n} {A : Set ℓ} {B : Set m} {{_ : Eq A}} (ρ : A → B) {a : A} {as : Vector A n} {bs : Vector B n} {k : Fin n} →
  vdistinct as →
  a ∈v as at k →
  (ρ v[ as ↦ bs ]) a ≡ bs ! k
vupdate-∈at ρ dst-as a∈asatk = {!   !}

vcons : ∀ {ℓ n} {A : Set ℓ} → A → Vector A n → Vector A (suc n)
vcons a as = a ∷ as

-- for some reason the following is yellow...
-- vcons-≡1 : ∀ {ℓ n} {A : Set ℓ} {a b : A} {as bs : Vector A n} → a ∷ as ≡ b ∷ bs → a ≡ b ∧ as ≡ bs
vcons-≡1 : ∀ {ℓ n} {A : Set ℓ} {a b : A} {as bs : Vector A n} → vcons a as ≡ vcons b bs → a ≡ b ∧ as ≡ bs
vcons-≡1 refl = refl , refl

-- vcons-≡2 : ∀ {ℓ} {n} {A : Set ℓ} {a b : A} {as bs : Vector A n} → a ≡ b → as ≡ bs → a ∷ as ≡ b ∷ bs
-- vcons-≡2 refl refl = refl

-- infix 30 _\\v_
-- _\\v_ : ∀ {ℓ m n} {A : Set ℓ} {{_ : Eq A}} → Vector A m → Vector A n → Vector A ?
-- ε \\v _ = ε
-- (a ∷ as) \\v bs with a ∈v? bs
-- ... | yes = as \\v bs
-- ... | no = a ∷ (as \\v bs)

indices : (n : ℕ) → Vector (Fin n) n
indices 0 = ε
indices (suc n) = fzero ∷ vmap fsuc (indices n)

indices-Lemma : ∀ {ℓ n} {A : Set ℓ} (as : Vector A n) → vmap (λ i → as ! i) (indices n) ≡ as
indices-Lemma as = {!   !}

indices-! : ∀ {n : ℕ} (k : Fin n) → indices n ! k ≡ k
indices-! fzero = refl
indices-! {suc n} (fsuc k) with indices-! k
... | ind = begin
  indices (suc n) ! (fsuc k) ≡⟨⟩
  vmap fsuc (indices n) ! k ≡⟨ vmap-! (indices n) ⟩
  fsuc (indices n ! k) ≡⟨ cong fsuc ind ⟩
  fsuc k
  ∎
  
instance
  eqVector : ∀ {ℓ} {n : ℕ} {A : Set ℓ} {{_ : Eq A}} → Eq (Vector A n)
  _≡?_ {{eqVector {ℓ} {n} {A}}} = go where

    go : (xs : Vector A n) → (ys : Vector A n) → Dec (xs ≡ ys)
    go ε ε = yes {proof = refl}
    go (x ∷ xs) (y ∷ ys) with x ≡? y
    ... | no {proof} = no {proof = λ p → proof (fst (vcons-≡1 p))}
    ... | yes {proof = refl} with xs ≡? ys
    ... | yes {proof = refl} = yes {proof = refl}
    ... | no {proof} = no {proof = λ p → proof (snd (vcons-≡1 p))}
