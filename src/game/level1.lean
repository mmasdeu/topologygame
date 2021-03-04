import game.definition -- hide

/- Tactic : refl

## Summary

`refl` proves goals of the form `X = X`.

## Details

The `refl` tactic will close any goal of the form `A = B`
where `A` and `B` are *exactly the same thing*.

### Example:
If it looks like this in the top right hand box:
```
a b c d : mynat
⊢ (a + b) * (c + d) = (a + b) * (c + d)
```

then

`refl,`

will close the goal and solve the level. Don't forget the comma.

-/


/- Tactic : rw

## Summary

If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. Variants: `rw ← h` (changes
`Y` to `X`) and
`rw h at h2` (changes `X` to `Y` in hypothesis `h2` instead
of the goal).

## Details

The `rw` tactic is a way to do "substituting in". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s. 

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).
For example, in world 1 level 4
we learn about `add_zero x : x + 0 = x`, and `rw add_zero`
will change `x + 0` into `x` in your goal (or fail with
an error if Lean cannot find `x + 0` in the goal).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw h` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l` and
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:
```
x y : mynat
h : x = y + y
⊢ succ (x + 0) = succ (y + y)
```

then

`rw add_zero,`

will change the goal into `⊢ succ x = succ (y + y)`, and then

`rw h,`

will change the goal into `⊢ succ (y + y) = succ (y + y)`, which
can be solved with `refl,`.

### Example: 
You can use `rw` to change a hypothesis as well. 
For example, if your local context looks like this:
```
x y : mynat
h1 : x = y + 3
h2 : 2 * y = x
⊢ y = 3
```
then `rw h1 at h2` will turn `h2` into `h2 : 2 * y = y + 3`.
-/

/- Tactic : exact

## Summary 

If the goal is `⊢ X` then `exact x` will close the goal if
and only if `x` is a term of type `X`. 

## Details

Say $P$, $Q$ and $R$ are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this: 

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j(h(p)),`

because $j(h(p))$ is easily checked to be a term of type $R$
(i.e., an element of the set $R$, or a proof of the proposition $R$).

-/

/- Tactic : intro

## Summary:

`intro p` will turn a goal `⊢ P → Q` into a hypothesis `p : P`
and goal `⊢ Q`. If `P` and `Q` are sets `intro p` means "let $p$ be an arbitrary element of $P$".
If `P` and `Q` are propositions then `intro p` says "assume $P$ is true". 

## Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. `intro p` turns

`⊢ P → Q`

into 

```
p : P
⊢ Q
```

The opposite tactic to intro is `revert`; given the situation
just above, `revert p` turns the goal back into `⊢ P → Q`.

## Example

If your goal is an implication $P\implies Q$ then Lean writes
this as `⊢ P → Q`, and `intro p,` can be thought of as meaning
"let $p$ be a proof of $P$", or more informally "let's assume that
$P$ is true". The goal changes to `⊢ Q` and the hypothesis `p : P`
appears in the local context.
-/

/- Tactic : apply

## Summary

If `h : P → Q` is a hypothesis, and the goal is `⊢ Q` then
`apply h` changes the goal to `⊢ P`. 

## Details

If you have a function `h : P → Q` and your goal is `⊢ Q`
then `apply h` changes the goal to `⊢ P`. The logic is
simple: if you are trying to create a term of type `Q`,
but `h` is a function which turns terms of type `P` into
terms of type `Q`, then it will suffice to construct a
term of type `P`. A mathematician might say: "we need
to construct an element of $Q$, but we have a function $h:P\to Q$
so it suffices to construct an element of $P$". Or alternatively
"we need to prove $Q$, but we have a proof $h$ that $P\implies Q$
so it suffices to prove $P$".

-/

/- Tactic : exfalso

## Summary

Changes the goal to `⊢ false`.

## Details

This may seem hard to prove,
but it is useful when we have a contradiction in the hypotheses.

For example, if we have `h : ¬ P` as a hypothesis and we apply `exfalso`
we can then `apply h` to transform the goal into `⊢ P`.

-/

/- Axiom : The total set (called `univ`) is open.
univ_mem : is_open set.univ
-/

/- Axiom : The intersection of two open sets is open.
inter : ∀ (U V : set X) (hA : is_open U) (hB : is_open V), is_open (U ∩ V)
-/

/- Axiom : The union of an arbitrary set of open sets is open.
union : ∀ (Y : set (set X)) (h : ∀ U ∈ Y, is_open U), is_open (⋃₀ Y)
-/

/- Axiom : The union over the empty set is empty.
sUnion_empty : ⋃₀ ∅ = ∅
-/

/-
# Level 1 : The empty set is open.
-/
noncomputable theory -- hide
open set -- hide

/-
In many textbooks, one of the axioms of a topological space is that the empty set is open. This actually follows from the other axioms!
-/

namespace topological_space -- hide


/- Hint : Click here for a hint, in case you get stuck.
In Lean, sets are notation for logical statements. That is, the set
`a ∈ { x : X | P x }` means *the same as* `P a`. As a somewhat degenerate
example, `a ∈ ∅` means `false`.
-/

/- Lemma
Prove that the empty set is open.
-/
lemma empty_mem {X : Type} [topological_space X] : is_open (∅ : set X) :=
begin
  rw ←sUnion_empty,
  apply union,
  tauto,







end

end topological_space -- hide