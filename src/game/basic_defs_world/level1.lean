import game.basic_defs_world.definition -- hide


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
lemma is_open_empty {X : Type} [topological_space X] : is_open (∅ : set X) :=
begin
  rw ←sUnion_empty,
  apply union,
  tauto,







end

end topological_space -- hide