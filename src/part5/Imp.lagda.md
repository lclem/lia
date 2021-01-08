---
title: "Imperative programs 🚧"
---

```
{-# OPTIONS --allow-unsolved-metas #-}
module part5.Imp where
open import part5.Exp hiding (_↝_; _,_⇒_; ⇒-det; ↝*-trans; _↝*⟨⟩_; _↝⟨_⟩_; _↝*⟨_⟩_; _,_↝_,_)
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

# Big-steps operational semantics (Natural semantics)

We begin with the notion of state,
which is the same as environments as of now,
but needs not be.

```
State = VarName → ℕ

private
  variable
    m n : ℕ
    s s′ s′′ : State
    x : VarName
    e : AExp
    b : BExp
    c d c′ d′ : Cmd
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
  ⇒-skip :
    ------------
    skip , s ⇒ s
```

### `x ≔ e`

The assignment command modifies the state
by updating the value of `x` to the value of `e` in the current state.

```
  ⇒-assign :
    -----------------------------
    x ≔ e , s ⇒ s [ x ↦ A⟦ e ⟧ s ]
```

### `c ⨟ d`

Sequencing two commands amounts to thread the state change.

```
  ⇒-seq :
    c , s ⇒ s′ →
    d , s′ ⇒ s′′ →
    ---------------
    c ⨟ d , s ⇒ s′′
```

### `if b then c else d`

For conditionals, there are two cases to consider,
depending on whether the condition evaluates to true or to false.

```
  ⇒-if-tt :
    B⟦ b ⟧ s ≡ tt →
    c , s ⇒ s′ →
    ---------------------------
    if b then c else d , s ⇒ s′
    
  ⇒-if-ff :
    B⟦ b ⟧ s ≡ ff →
    d , s ⇒ s′ →
    ---------------------------
    if b then c else d , s ⇒ s′
```

### `while b do: c`

Similarly, for while loops there are two cases to consider.

```
  ⇒-while-tt :
    B⟦ b ⟧ s ≡ tt →
    c , s ⇒ s′ →
    while b do: c , s′ ⇒ s′′ →
    --------------------------
    while b do: c , s ⇒ s′′
  
  ⇒-while-ff :
    B⟦ b ⟧ s ≡ ff →
    ---------------------
    while b do: c , s ⇒ s
```

This concludes the definition of the operational semantics `c , s ⇒ s′`.

## **Exercise**: `do: c while b`

Extend the syntax and semantics of programs
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
⇒-det : c , s ⇒ s′ →
        c , s ⇒ s′′ →
        -------------
        s′ ≡ s′′

⇒-det ⇒-skip ⇒-skip = refl
⇒-det ⇒-assign ⇒-assign = refl
⇒-det (⇒-seq δ₁ δ₂) (⇒-seq δ₃ δ₄) rewrite ⇒-det δ₁ δ₃ | ⇒-det δ₂ δ₄ = refl
⇒-det (⇒-if-tt _ δ1) (⇒-if-tt _ δ2) rewrite ⇒-det δ1 δ2 = refl
⇒-det (⇒-if-tt ⟦b⟧s≡tt _) (⇒-if-ff ⟦b⟧s≡ff _) = a≡ff→a≡tt-elim ⟦b⟧s≡ff ⟦b⟧s≡tt
⇒-det (⇒-if-ff ⟦b⟧s≡ff _) (⇒-if-tt ⟦b⟧s≡tt _) = a≡ff→a≡tt-elim ⟦b⟧s≡ff ⟦b⟧s≡tt
⇒-det (⇒-if-ff _ δ₁) (⇒-if-ff _ δ₂) rewrite ⇒-det δ₁ δ₂ = refl
⇒-det (⇒-while-tt _ δ₁ δ₂) (⇒-while-tt _ δ₃ δ₄) rewrite ⇒-det δ₁ δ₃ | ⇒-det δ₂ δ₄ = refl
⇒-det (⇒-while-tt ⟦b⟧s≡tt _ _) (⇒-while-ff ⟦b⟧s≡ff) = a≡ff→a≡tt-elim ⟦b⟧s≡ff ⟦b⟧s≡tt
⇒-det (⇒-while-ff ⟦b⟧s≡ff) (⇒-while-tt ⟦b⟧s≡tt _ _) = a≡ff→a≡tt-elim ⟦b⟧s≡ff ⟦b⟧s≡tt
⇒-det (⇒-while-ff _) (⇒-while-ff _) = refl
```

## **Exercise**: `loop`

Show that the program `loop` introduced above never stops.

```
loop-⊥ : ~ (loop , s ⇒ s′)
loop-⊥ (⇒-while-tt _ ⇒-skip δ) = loop-⊥ δ
loop-⊥ (⇒-while-ff ⟦tt⟧s≡ff) = tt≡ff-elim ⟦tt⟧s≡ff
```

## Behavioural equivalence

Two programs `c`, `d` are *behaviourally equivalent*, written `c ∼ d`, if they relate the same set of initial and final states:

```
infix 10 _∼_
_∼_ : (c d : Cmd) → Set
c ∼ d = ∀[ s ] ∀[ s′ ] c , s ⇒ s′ ↔ d , s ⇒ s′

sym-∼ : c ∼ d → d ∼ c
sym-∼ c∼d s s′ with c∼d s s′
... | have0 , have1 = have1 , have0
```

Examples:

```
skip-⨟-id-left : ∀ c → skip ⨟ c ∼ c
skip-⨟-id-left c s s′ = (λ{ (⇒-seq ⇒-skip δ) → δ}) , λ δ → ⇒-seq ⇒-skip δ

skip-⨟-id-right : ∀ c → c ⨟ skip ∼ c
skip-⨟-id-right c s s′ = (λ{ (⇒-seq δ ⇒-skip) → δ}) , λ δ → ⇒-seq δ ⇒-skip

assoc-⨟ : ∀ c d e → (c ⨟ d) ⨟ e ∼ c ⨟ (d ⨟ e)
assoc-⨟ c d e s s′ = {!   !} , {!   !}
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
    x ≔ e , s ↝ skip , s [ x ↦ A⟦ e ⟧ s ]
```

### `c ⨟ d`

In the case of sequencing `c ⨟ d`,
where are two cases.

In the case `↝-seq-left`, we evaluate one step of `c`.
In the case `↝-seq-right`, `c` has finished and we continue with `d`.

```
  ↝-seq-left : ∀ {c s c′ s′ d} →
    c , s ↝ c′ , s′ →
    c ⨟ d , s ↝ c′ ⨟ d , s′
    
  ↝-seq-right : ∀ {d s} →
    skip ⨟ d , s ↝ d , s
```

### `if b then c else d`

The conditional has two symmetric cases,
depending on whether the condition evaluates to `true` or `false`.

```
  ↝-if-tt : ∀ {b s c d} →
    B⟦ b ⟧ s ≡ tt →
    if b then c else d , s ↝ c , s
    
  ↝-if-ff : ∀ {b s c d} →
    B⟦ b ⟧ s ≡ ff →
    if b then c else d , s ↝ d , s
```

### `while b do: c`

The while looping construct also has two cases.
If the condition `b` evaluates to true,
then the command rewrites to `c ⨟ while b do: c`.
Otherwise, it terminates rewriting to `skip`.

```
  ↝-while-tt : ∀ {b c s} →
    B⟦ b ⟧ s ≡ tt →
    while b do: c , s ↝ c ⨟ while b do: c , s
    
  ↝-while-ff : ∀ {b c s} →
    B⟦ b ⟧ s ≡ ff →
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
↝*-trans stop δ₂ = δ₂
↝*-trans (one step δ₁) δ₂ = one step (↝*-trans δ₁ δ₂)
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
⨟-lemma-1 : ∀ {c d s s′ s′′} →
  c , s ↝* skip , s′′ →
  d , s′′ ↝* skip , s′ →
  c ⨟ d , s ↝* skip , s′
⨟-lemma-1 stop der2 = one ↝-seq-right der2
⨟-lemma-1 {c} {d} {s} {s′} {s′′} (one {y = c′ , s′′′} der0 der1) der2
    with ⨟-lemma-1 der1 der2
... | der = start
              c ⨟ d , s ↝⟨ ↝-seq-left der0 ⟩
              c′ ⨟ d , s′′′ ↝*⟨ der ⟩
              skip , s′ 
            end
```

## **Exercise**: `big→small`

Once we have two alternative semantics for imperative programs,
the question arises as to whether they are equivalent.

We show that the big steps and the small steps operational semantics of imperative programs yield the same results.
There are two directions to show.

We begin in this section with the easier direction `big→small`:
the big step semantics implies the small step one.

```
big→small : ∀ c s s′ → c , s ⇒ s′ → c , s ↝* skip , s′
```

### `skip`, `x ≔ e`

The proofs for the skip and assignment constructs are immediate.

```
big→small skip s .s ⇒-skip = stop
big→small (x ≔ e) s .(s [ x ↦ A⟦ e ⟧ s ]) ⇒-assign = one ↝-assign stop
```

### `c ⨟ d`

In the case of sequencing `c ⨟ d`
we call the inductive assumption twice and we collect the results.

```
big→small (c ⨟ d) s s′ (⇒-seq {s′ = s′′} ⇒-der1 ⇒-der2)
    with big→small c s s′′ ⇒-der1 | big→small d s′′ s′ ⇒-der2
... | ↝*-der1 | ↝*-der2 =
  start
    c ⨟ d , s ↝*⟨ ⨟-lemma-1 ↝*-der1 ↝*-der2 ⟩
    skip , s′
  end
```

### `if b then c else d`

The conditional construct has two cases,
depending on whether the condition holds or not.

```
big→small (if b then c else d) s s′ (⇒-if-tt b≡true ⇒-der)
    with big→small c s s′ ⇒-der
... | ↝*-der =
  start
    if b then c else d , s ↝⟨ ↝-if-tt b≡true ⟩
    c , s ↝*⟨ ↝*-der ⟩
    skip , s′
  end

big→small (if b then c else d) s s′ (⇒-if-ff b≡false ⇒-der)
    with big→small d s s′ ⇒-der
... | ↝*-der =
  start
    if b then c else d , s ↝⟨ ↝-if-ff b≡false ⟩
    d , s ↝*⟨ ↝*-der ⟩
    skip , s′
  end
```

### `while b do: c`

Finally, also for while loops there are two cases,
depending on whether the guard `b` holds or not.
In the `true` case we apply the inductive assumption twice.

```
big→small (while b do: c) s s′ (⇒-while-tt {s′ = s′′} b≡true ⇒-der1 ⇒-der2)
    with big→small c s s′′ ⇒-der1 | big→small (while b do: c) s′′ s′ ⇒-der2
... | ↝*-der1 | ↝*-der2 =
  start
    while b do: c , s ↝⟨ ↝-while-tt b≡true ⟩
    c ⨟ while b do: c , s  ↝*⟨ ⨟-lemma-1 ↝*-der1 ↝*-der2 ⟩
    skip , s′
  end  

big→small (while b do: c) s .s (⇒-while-ff b≡false) =
  start
    while b do: c , s ↝⟨ ↝-while-ff b≡false ⟩
    skip , s
  end
```

## From small to big steps: first attempt

We turn now our attention to the other direction of the equivalence between small and big steps operational semantics,
namely

```
-- small→big : ∀ c s s′ → c , s ↝* skip , s′ → c , s ⇒ s′
```

A natural starting point is the converse of `⨟-lemma-1` above.

```
-- ⨟-lemma-2 : ∀ {c d s s′} → c ⨟ d , s ↝* skip , s′ → ∃[ s′′ ] c , s ↝* skip , s′′ × d , s′′ ↝* skip , s′
```

However, it turns out that the statement `small→big` above
creates problems for the termination checker in first `while` case
(all the other cases go through):

```
-- small→big (while b do: c) s s′ (one (↝-while-tt b≡true) ↝*-der)
--     with ⨟-lemma-2 ↝*-der
-- ... | s′′ , ↝*-der1 , ↝*-der2
--     with small→big c s s′′ ↝*-der1 |
--          ? {- small→big (while b do: c) s′′ s′ ↝*-der2 -}
-- ... | ⇒-der1 | ⇒-der2 = ⇒-while-tt b≡true ⇒-der1 ⇒-der2
-- small→big _ _ _ _ = ?
```

The issue with the commented code above
is that no argument of the call

```
-- small→big (while b do: c) s′′ s′ ↝*-der2
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
but we won′t need it here.)


```
⨟-lemma-2 : ∀ {c d s s′ m} →
  c ⨟ d , s ↝* skip , s′ # m →
  ∃[ s′′ ] ∃[ m1 ] ∃[ m2 ]
      c , s ↝* skip , s′′ # m1 ×
      d , s′′ ↝* skip , s′ # m2 ×
      suc (m1 +ℕ m2) ≡ m
⨟-lemma-2 (one (↝-seq-left step) ↝-der)
    with ⨟-lemma-2 ↝-der
... | s′′ , m1 , m2 , der1 , der2 , m1+m2≡n =
    s′′ , suc m1 , m2 , one step der1 , der2 , cong suc m1+m2≡n
⨟-lemma-2 {s = s} (one {n = n} ↝-seq-right ↝-der) =
    s , 0 , n , stop , ↝-der , refl
```

### **Exercise**: `skip` and `↝*`

Show that executing the `skip` command necessarily terminates in `0` steps.

*Hint*: Convince Agda that only the case `stop` needs to be considered.

```
↝*-skip : skip , s ↝* c , s′ # m →
          -------------------------
          c ≡ skip × s ≡ s′ × m ≡ 0
↝*-skip stop = refl , refl , refl
```

## **Exercise**: `small→big`

We are now ready to prove that the small step semantics implies the big step one.

```
small→big : ∀ c s s′ n → c , s ↝* skip , s′ # n → c , s ⇒ s′
small→big c s s′ n ↝*-der = go c s s′ n ↝*-der (<-wf n) where

 go : ∀ c s s′ n → c , s ↝* skip , s′ # n → Acc _<_ n → c , s ⇒ s′
```

We employ a helper function `go`
which has an additional parameter `Acc n`
allowing us to do well-founded induction in the crucial `while` case below.

### `skip`

The `skip` case is immediate.

```
 go skip s .s 0 stop _ = ⇒-skip
```

### `x ≔ e`

In the assignment case we call `↝*-skip ↝*-der`
to enure that `s′ ≡ s [ x ↦ ⟦ e ⟧A s ]`
as required by `⇒-assign`.

```
 go (x ≔ e) s s′ (suc m) (one ↝-assign ↝*-der) _
     with ↝*-skip ↝*-der
 ... | refl , refl , refl = ⇒-assign
```

### `c ⨟ d`

In the sequencing case
we first call `⨟-lemma-2 ↝*-der` to discover that

1. `↝*-der1 : c , s ↝* skip , s′′ # _`, and
2. `↝*-der2 : d , s′′ ↝* skip , s′ # _`.

With this information in hand,
we recursively call `small→big` on the subcomputations
`↝*-der1`, `↝*-der2` and we assemble the results back with `⇒-seq`.

```
 go (c ⨟ d) s s′ (suc m) ↝*-der (acc a)
     with ⨟-lemma-2 ↝*-der
 ... | s′′ , m1 , m2 , ↝*-der1 , ↝*-der2 , _
     with go c s s′′ m1 ↝*-der1 (a m1 {!   !}) | go d s′′ s′ m2 ↝*-der2 {!   !}
 ... | ⇒-der1 | ⇒-der2 = ⇒-seq ⇒-der1 ⇒-der2
```

Note how we do not need to reason about the lengths `m1`, `m2` of the two subcomputations `↝*-der1`, `↝*-der2`
because the recursive calls `small→big c ...` and `small→big d`
are done on structurally smaller programs `c`, resp., `d`.

### `if b then c else d`

The case for conditional is straightforward.

```
 go (if b then c else d) s s′ (suc m) (one (↝-if-tt b≡true) ↝*-der) _
     with go c s s′ m ↝*-der {!   !}
 ... | ⇒-der = ⇒-if-tt b≡true ⇒-der

 go (if b then c else d) s s′ (suc m) (one (↝-if-ff b≡false) ↝*-der) _
     with go d s s′ m ↝*-der {!   !}
 ... | ⇒-der = ⇒-if-ff b≡false ⇒-der
```

### `while b do: c`, case one

We now tackle the hardest case,
the while loop when the guard evaluates to true.

By calling `⨟-lemma-2 ↝*-der`
we obtain `m1` as the length of
the derivation `↝*-der1` showing `c , s ↝* skip , s′′ # m1`
and `m2` as the length of
`↝*-der2` showing `while b do: c , s′′ ↝* skip , s′ # m2`
and a proof `sm1+m2≡m` that `suc (m1 + m2) ≡ m`.

We can then show that `m1 < m` and `m2 < m`,
which allows us to use well-founded induction when calling `go` again
on `↝*-der1`, resp., `↝*-der2`.

The latter inductive calls to `go`
provide us with `⇒-der1 : c , s ⇒ s′′`
and `⇒-der2 : while b do: c , s′′ ⇒ s′`,
from which we can immediately conclude by applying the constructor `⇒-while-tt`

```
 go (while b do: c) s s′ m (one (↝-while-tt b≡true) ↝*-der) (acc a)
     with ⨟-lemma-2 ↝*-der
 ... | s′′ , m1 , m2 , ↝*-der1 , ↝*-der2 , sm1+m2≡m
     with go c s s′′ m1 ↝*-der1 (a m1 m1<m) |
          go (while b do: c) s′′ s′ m2 ↝*-der2 (a m2 m2<m)
          where
           m1<m : m1 < m
           m1<m = {!   !} -- s≤s (≤-suc2 (subst (λ x → suc m1 ≤ x) sm1+m2≡m (≤-+-left {suc m1} {m2})))
           m2<m : m2 < m
           m2<m = {!   !} -- s≤s (subst (m2 ≤_) sm1+m2≡m (≤-+-right {suc m1} {m2}))
 ... | ⇒-der1 | ⇒-der2 = ⇒-while-tt b≡true ⇒-der1 ⇒-der2
```

This is the only place where we use well-founded induction.

### `while b do: c`, case two

This case is straightforward.

```
 go (while b do: c) s s′ m (one (↝-while-ff b≡false) ↝*-der) _
     with ↝*-skip ↝*-der
 ... | refl , refl , refl = ⇒-while-ff b≡false
```

# Contexual equivalence

We first need to introduce the notion of  *program contexts*,
which are programs with a single distinguished hole.

```
data Context : Set where
  □ : Context
  _⨟-left_ : (C : Context) → (c : Cmd) → Context
  _⨟-right_ : (c : Cmd) → (C : Context) → Context
  if-left_then_else_ : (b : BExp) → (C : Context) → (c : Cmd) → Context
  if-right_then_else_ : (b : BExp) → (c : Cmd) → (C : Context) → Context
  while_do:_ : (b : BExp) → (C : Context) → Context

private
  variable
    C : Context
```

We can fill the hole in a context with a given program.

```
contextApply : Context → Cmd → Cmd
contextApply □ d = d
contextApply (C ⨟-left c) d = contextApply C d ⨟ c
contextApply (c ⨟-right C) d = c ⨟ contextApply C d
contextApply (if-left b then C else c) d = if b then (contextApply C d) else c
contextApply (if-right b then c else C) d = if b then c else (contextApply C d)
contextApply (while b do: C) d = while b do: contextApply C d
```

Contexual equivalence:

```
_≈_ : (c d : Cmd) → Set
c ≈ d = ∀ C → contextApply C c ∼ contextApply C d
```

Preliminary facts:

```
fa-⨟-left : ∀ C →
           contextApply C c ∼ contextApply C d →
           contextApply C c ⨟ c′ , s ⇒ s′ →
           -------------------------------------
           contextApply C d ⨟ c′ , s ⇒ s′

fa-⨟-left {s = s} _ Cc∼Cd (⇒-seq {s′ = s′′} δ₀ δ₁)
    with Cc∼Cd s s′′
... | have , _ = ⇒-seq (have δ₀) δ₁

fa-⨟-right : ∀ C →
            contextApply C c ∼ contextApply C d →
            c′ ⨟ contextApply C c , s ⇒ s′ →
            -------------------------------------
            c′ ⨟ contextApply C d , s ⇒ s′

fa-⨟-right {s′ = s′} _ Cc∼Cd (⇒-seq {s′ = s′′} δ₀ δ₁)
    with Cc∼Cd s′′ s′
... | have , _ = ⇒-seq δ₀ (have δ₁)

fa-while : ∀ C →
           contextApply C c ∼ contextApply C d →
           while b do: contextApply C c , s ⇒ s′ →
           ---------------------------------------
           while b do: contextApply C d , s ⇒ s′
           
fa-while _ Cc∼Cd (⇒-while-ff ⟦b⟧s≡ff) = ⇒-while-ff ⟦b⟧s≡ff

fa-while C Cc∼Cd (⇒-while-tt {s′′ = s′′} ⟦b⟧s≡tt δ₀ δ₁)
  with fst (Cc∼Cd _ _) δ₀ |
       fa-while C Cc∼Cd δ₁
... | δ₀′ | δ₁′ = ⇒-while-tt ⟦b⟧s≡tt δ₀′ δ₁′

fa-ite-right : ∀ C →
               contextApply C c ∼ contextApply C d →
               if b then contextApply C c else c′ , s ⇒ s′ →
               --------------------------------------------
               if b then contextApply C d else c′ , s ⇒ s′

fa-ite-right C Cc∼Cd (⇒-if-tt ⟦b⟧s≡tt δ)
  with fst (Cc∼Cd _ _) δ
... | δ′ = ⇒-if-tt ⟦b⟧s≡tt δ′

fa-ite-right C Cc∼Cd (⇒-if-ff ⟦b⟧s≡ff δ) = ⇒-if-ff ⟦b⟧s≡ff δ

fa-ite-left : ∀ C →
              contextApply C c ∼ contextApply C d →
              if b then c′ else contextApply C c , s ⇒ s′ →
              --------------------------------------------
              if b then c′ else contextApply C d , s ⇒ s′

fa-ite-left C Cc∼Cd (⇒-if-tt ⟦b⟧s≡tt δ) = ⇒-if-tt ⟦b⟧s≡tt δ
fa-ite-left C Cc∼Cd (⇒-if-ff ⟦b⟧s≡ff δ)
  with fst (Cc∼Cd _ _) δ
... | δ′ = ⇒-if-ff ⟦b⟧s≡ff δ′
```

The natural semantics is fully abstract:

```
congruence-1 : c ≈ d → c ∼ d
congruence-1 c≈d = c≈d □

congruence-2 : c ∼ d → c ≈ d

congruence-2 c∼d □ s s′ = c∼d s s′

congruence-2 {c} {d} c∼d (C ⨟-left c′) s s′
    with congruence-2 c∼d C
... | ind = goal0 , goal1 where

  goal0 : contextApply C c ⨟ c′ , s ⇒ s′ → contextApply C d ⨟ c′ , s ⇒ s′
  goal0 = fa-⨟-left C ind

  goal1 : contextApply C d ⨟ c′ , s ⇒ s′ → contextApply C c ⨟ c′ , s ⇒ s′
  goal1 = fa-⨟-left C (sym-∼ ind)

congruence-2 c∼d (c ⨟-right C) s s′
  with congruence-2 c∼d C
... | ind = fa-⨟-right C ind , fa-⨟-right C (sym-∼ ind)

congruence-2 {c} {d} c∼d (if-left b then C else c′) s s′
    with congruence-2 c∼d C
... | ind = fa-ite-right C ind , fa-ite-right C (sym-∼ ind)

congruence-2 {c} {d} c∼d (if-right b then c′ else C) s s′
    with congruence-2 c∼d C
... | ind = fa-ite-left C ind , fa-ite-left C (sym-∼ ind)

congruence-2 {c} {d} c∼d (while b do: C) s s′
  with congruence-2 c∼d C
... | ind = goal0 , goal1 where

  goal0 : (while b do: contextApply C c) , s ⇒ s′ →
          (while b do: contextApply C d) , s ⇒ s′
  goal0 = fa-while C ind

  goal1 : (while b do: contextApply C d) , s ⇒ s′ →
          (while b do: contextApply C c) , s ⇒ s′
  goal1 = fa-while C (sym-∼ ind)
  
congruence : c ≈ d ↔ c ∼ d
congruence = congruence-1 , congruence-2
```

# Axiomatic semantics

TODO.