import data.set.basic -- hide
open set -- hide
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

/-
In this level we introduce the new tactic `apply`. Look at what it does and try to solve it!
-/

/- Hint : Click here for a hint, in case you get stuck.
Start with an `intro`, then try to `apply` the right hypothesis.
-/

variables {X Y : Type} -- hide

/- Lemma : no-side-bar
If A, B and C are sets and x ∈ A, and we know that x ∈ A → x ∈ B and that x ∈ B → x ∈ C, then
we can deduce that x ∈ C.
-/
lemma subset_transitive_basic (A B C : set X) (x : X) (hAB : x ∈ A → x ∈ B) (hBC : x ∈ B → x ∈ C) :
  x ∈ A → x ∈ C :=
begin
  intro h,
  apply hBC,
  apply hAB,
  exact h,

  
end

