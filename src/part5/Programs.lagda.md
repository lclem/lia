---
title: "Imperative programs 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Programs where
open import part5.BExp hiding (_,_⇒_; ⇒-det; ↝*-trans; _↝*⟨⟩_; _↝⟨_⟩_; _↝*⟨_⟩_) public
```

```
infixr 20 _⨟_
infix 25 _≔_
```

# Syntax of programs 

We define a simple imperative language,
leveraging on arithmetic and boolean expressions defined above.

```
data Cmd : Set where
  skip : Cmd
  _≔_ : VarName → AExp → Cmd
  _⨟_ : Cmd → Cmd → Cmd
  if_then_else_ : BExp → Cmd → Cmd → Cmd
  while_do:_ : BExp → Cmd → Cmd
```

For example, the following is a valid program (piece of syntax).

```
loop : Cmd
loop = while tt do: skip
```

(We added a colon in the syntax of `while_do:_`
because `do` is a reserved keyword.)

# Denotational semantics

It may come as a surprise,
but it is not possible to define the semantics of imperative programs as an Agda function,
because Agda allows only terminating (i.e., total) functions.
On the other hand, imperative programs, such as `loop` above, may not terminate.

Therefore, we resort to an operational semantics.

## Big-steps operational semantics

We begin with the notion of state,
which is the same as environments as of now,
but needs not be.

```
State = VarName → ℕ
```

The definition of the operational semantics of imperative programs
follows a case analysis.

```
infix 4 _,_⇒_
data _,_⇒_ : Cmd → State → State → Set where
```

### `skip`

The `skip` command terminates immediately without changing the state.

```
  ⇒-skip : ∀ {s} →
    skip , s ⇒ s
```

### `x ≔ e`

The assignment command modifies the state
by updating the value of `x` to the value of `e` in the current state.

```
  ⇒-assign : ∀ {s x e} →
    x ≔ e , s ⇒ s [ x ↦ ⟦ e ⟧ s ]
```

### `c ⨟ d`

Sequencing two commands amounts to thread the state change.

```
  ⇒-seq : ∀ {c d s s' s''} →
    c , s ⇒ s' →
    d , s' ⇒ s'' →
    c ⨟ d , s ⇒ s''
```

### `if b then c else d`

For conditionals, there are two cases to consider,
depending on whether the condition evaluates to true or to false.

```
  ⇒-if-tt : ∀ {b s c s' d} →
    ⟦ b ⟧B s ≡ tt →
    c , s ⇒ s' →
    if b then c else d , s ⇒ s'
    
  ⇒-if-ff : ∀ {b s c s' d} →
    ⟦ b ⟧B s ≡ ff →
    d , s ⇒ s' →
    if b then c else d , s ⇒ s'
```

### `while b do: c`

Similarly, for while loops there are two cases to consider.

```
  ⇒-while-tt : ∀ {b s c s' s''} →
    ⟦ b ⟧B s ≡ tt →
    c , s ⇒ s' →
    while b do: c , s' ⇒ s'' →
    while b do: c , s ⇒ s''
  
  ⇒-while-ff : ∀ {b s c} →
    ⟦ b ⟧B s ≡ ff →
    while b do: c , s ⇒ s
```

This concludes the definition of the operational semantics ` c , s ⇒ s'`.

## **Exercise**: `do: c while b`

Extend the syntax and semantics of imperative programs
by adding a new construct

```
-- do: c while b
```

where `c` is a command and `b` a boolean expression.
The informal semantics of the do-while construct
is to first execute `c`,
and then evaluate the guard `b`:
If it evaluates to true, then we repeat the process,
otherwise we exit the loop.

## **Exercise**: Determinism

Since we cannot encode the semantics of imperative programs as a function,
we immediately lose some properties which are for free for functions.

One example is deterministic evaluation.
Consequently, we need to prove separately
that evaluation of programs is deterministic.

Show that evaluation of imperative programs is deterministic.

```
-- convenient to rule out some impossible cases.
false≡true : {A : Set} → tt ≡ ff → A
false≡true ()

⇒-det : ∀ {c s s' s''} → c , s ⇒ s' → c , s ⇒ s'' → s' ≡ s''
⇒-det ⇒-skip ⇒-skip = {!   !}
⇒-det ⇒-assign ⇒-assign = {!   !}
⇒-det (⇒-seq der1 der2) (⇒-seq der3 der4) = {! ⇒-det der1 der2 !}
⇒-det (⇒-if-tt _ der1) (⇒-if-tt _ der2) = {!   !}
⇒-det (⇒-if-tt x _) (⇒-if-ff y _) = {!   !}
⇒-det (⇒-if-ff x _) (⇒-if-tt y _) = {!   !}
⇒-det (⇒-if-ff _ der1) (⇒-if-ff _ der2) = {!   !}
⇒-det (⇒-while-tt x der1 der2) (⇒-while-tt y der3 der4) = {!   !}
⇒-det (⇒-while-tt x _ _) (⇒-while-ff y) = {!   !}
⇒-det (⇒-while-ff x) (⇒-while-tt y _ _) = {!   !}
⇒-det (⇒-while-ff _) (⇒-while-ff _) = {!   !}
```

## **Exercise**: `loop`

Show that the program `loop` introduced above never stops.

```
loop-⊥ : ∀ {s s'} → ~ (loop , s ⇒ s')
loop-⊥ = {!   !}
```

# Small-steps operational semantics


We provide an alternative small-steps semantics for imperative programs.

### Configurations

```
Conf = Cmd × State -- Cartesian product
```

We treat configurations of the form `skip , s` as final,
hence there is no rule for the `skip` command.

```
infix 3 _↝_
data _↝_ : Conf → Conf → Set where
```

### `x ≔ e`

In the rule for assignment,
we just evaluate the arithmetic expression `e`
and update the state accordingly.

(We could have used the operational semantics of arithmetic expressions here,
but we avoid it for simplicity.
A similar remark applies to boolean expressions below.)

```
  ↝-assign : ∀ {x e s} →
    x ≔ e , s ↝ skip , s [ x ↦ ⟦ e ⟧ s ]
```

### `c ⨟ d`

In the case of sequencing `c ⨟ d`,
where are two cases.

In the case `↝-seq-left`, we evaluate one step of `c`.
In the case `↝-seq-right`, `c` has finished and we continue with `d`.

```
  ↝-seq-left : ∀ {c s c' s' d} →
    c , s ↝ c' , s' →
    c ⨟ d , s ↝ c' ⨟ d , s'
    
  ↝-seq-right : ∀ {d s} →
    skip ⨟ d , s ↝ d , s
```

### `if b then c else d`

The conditional has two symmetric cases,
depending on whether the condition evaluates to `true` or `false`.

```
  ↝-if-tt : ∀ {b s c d} →
    ⟦ b ⟧B s ≡ tt →
    if b then c else d , s ↝ c , s
    
  ↝-if-ff : ∀ {b s c d} →
    ⟦ b ⟧B s ≡ ff →
    if b then c else d , s ↝ d , s
```

### `while b do: c`

The while looping construct also has two cases.
If the condition `b` evaluates to true,
then the command rewrites to `c ⨟ while b do: c`.
Otherwise, it terminates rewriting to `skip`.

```
  ↝-while-tt : ∀ {b c s} →
    ⟦ b ⟧B s ≡ tt →
    while b do: c , s ↝ c ⨟ while b do: c , s
    
  ↝-while-ff : ∀ {b c s} →
    ⟦ b ⟧B s ≡ ff →
    while b do: c , s ↝ skip , s
```

## Transitive closure `↝*`

In order to formalise this, we first need to be able to combine many small steps together, i.e., we take the transitive closure of `_,_↝_,_`.

```
infix 3 _↝*_
data _↝*_ : Conf → Conf → Set where
  stop : ∀ {x} → x ↝* x
  one : ∀ {x y z} → x ↝ y → y ↝* z → x ↝* z
```

### **Exercise**: Transitivity

Show that the relation `↝*` on configurations is indeed transitive.
*Hint*: Do induction on `der1`.

```
↝*-trans : ∀ {x y z} → x ↝* y → y ↝* z → x ↝* z
↝*-trans der1 der2 = {!   !}
```

### Notation for transitive closure


The following suggestive notation will be useful for simplyfying carrying out proofs involving `↝*`.
They are entirely analogous to the chain of equalities constructed with `≡⟨⟩`.

```
infix  1 start_
infixr 2 _↝*⟨⟩_ _↝⟨_⟩_ _↝*⟨_⟩_
infix  3 _end

start_ : ∀ {x y} → x ↝* y → x ↝* y
start x↝*y = x↝*y

_↝*⟨⟩_ : ∀ x {y} → x ↝* y → x ↝* y
x ↝*⟨⟩ x↝*y = x↝*y

_↝⟨_⟩_ : ∀ x {y z} → x ↝ y → y ↝* z → x ↝* z
x ↝⟨ x↝y ⟩ y↝*z = one x↝y y↝*z

_↝*⟨_⟩_ : ∀ x {y z} → x ↝* y → y ↝* z → x ↝* z
x ↝*⟨ x↝*y ⟩ y↝*z = ↝*-trans x↝*y y↝*z

_end : ∀ x → x ↝* x
x end = stop
```

### **Exercise**: A lemma about `⨟`

Our objective is to show that small steps and big steps semantics agree.

Before showing this,
we need to prove a lemma
connecting sequencing `⨟` and `↝*`.

```
⨟-lemma-1 : ∀ {c d s s' s''} →
  c , s ↝* skip , s'' →
  d , s'' ↝* skip , s' →
  c ⨟ d , s ↝* skip , s'
⨟-lemma-1 stop der2 = {!   !}
⨟-lemma-1 {c} {d} {s} {s'} {s''} (one {y = c' , s'''} step der1) der2 = {!   !}
```

## **Exercise**: `big→small`

Once we have two alternative semantics for imperative programs,
the question arises as to whether they are equivalent.

We show that the big steps and the small steps operational semantics of imperative programs yield the same results.
There are two directions to show.

We begin in this section with the easier direction `big→small`:
the big step semantics implies the small step one.

```
big→small : ∀ c s s' → c , s ⇒ s' → c , s ↝* skip , s'
big→small = {!   !}
```

## From small to big steps: first attempt

We turn now our attention to the other direction of the equivalence between small and big steps operational semantics,
namely

```
-- small→big : ∀ c s s' → c , s ↝* skip , s' → c , s ⇒ s'
```

A natural starting point is the converse of `⨟-lemma-1` above.

```
-- ⨟-lemma-2 : ∀ {c d s s'} → c ⨟ d , s ↝* skip , s' → ∃[ s'' ] c , s ↝* skip , s'' × d , s'' ↝* skip , s'
```

However, it turns out that the statement `small→big` above
creates problems for the termination checker in first `while` case
(all the other cases go through):

```
-- small→big (while b do: c) s s' (one (↝-while-tt b≡true) ↝*-der)
--     with ⨟-lemma-2 ↝*-der
-- ... | s'' , ↝*-der1 , ↝*-der2
--     with small→big c s s'' ↝*-der1 |
--          ? {- small→big (while b do: c) s'' s' ↝*-der2 -}
-- ... | ⇒-der1 | ⇒-der2 = ⇒-while-tt b≡true ⇒-der1 ⇒-der2
-- small→big _ _ _ _ = ?
```

The issue with the commented code above
is that no argument of the call

```
-- small→big (while b do: c) s'' s' ↝*-der2
```

is structurally smaller than the original call.

What is missing here is an argument to convince the termination checker
that `↝*-der2` is "smaller" than ` ↝*-der`.
In order to formalise this, we need to refine the `↝*` relation
in order to take into account the *number* of derivation steps.

## Transitive closure with gas

The idea is to enrich the transitive closure relation
with the information about how many derivation steps have been made so far.

```
infix 3 _↝*_#_
data _↝*_#_ : Conf → Conf → ℕ → Set where
  stop : ∀ {x} → x ↝* x # 0
  one : ∀ {x y z n} → x ↝ y → y ↝* z # n → x ↝* z # suc n
```

In the base case `stop` we terminate the computation immediately with `0` number of steps,
and in the inductive case `one` we add an extra step
to the number of steps `n` performed inductively.

### **Exercise**: A second lemma about `⨟`

We can now prove the converse of `⨟-lemma-1` above
in the richer setting offered by `_↝*_#_`.

(Also `⨟-lemma-1` can be generalised to `_↝*_#_`,
but we won't need it here.)


```
⨟-lemma-2 : ∀ {c d s s' m} →
  c ⨟ d , s ↝* skip , s' # m →
  ∃[ s'' ] ∃[ m1 ] ∃[ m2 ]
      c , s ↝* skip , s'' # m1 ×
      d , s'' ↝* skip , s' # m2 ×
      suc (m1 +ℕ m2) ≡ m
⨟-lemma-2 (one (↝-seq-left step) ↝-der) = {!   !}
⨟-lemma-2 {s = s} (one {n = n} ↝-seq-right ↝-der) = {!   !}
```

### **Exercise**: `skip` and `↝*`

Show that executing the `skip` command necessarily terminates in `0` steps.

*Hint*: Convince Agda that only the case `stop` needs to be considered.

```
↝*-skip : ∀ {s c s' m} → skip , s ↝* c , s' # m → c ≡ skip × s ≡ s' × m ≡ 0
↝*-skip der = {!   !}
```

## **Exercise**: `small→big`

We are now ready to prove that the small step semantics implies the big step one.

```
small→big : ∀ c s s' n → c , s ↝* skip , s' # n → c , s ⇒ s'
small→big c s s' n ↝*-der = {!   !}

    -- go c s s' n ↝*-der (<-wf n) where

    -- go : ∀ c s s' n →  c , s ↝* skip , s' # n → Acc n → c , s ⇒ s'
    -- go = ?
 ```