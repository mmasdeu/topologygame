import data.set.basic
open set

/- Tactic : exfalso

## Summary

Changes the goal to `⊢ false`.

## Details

This may seem hard to prove,
but it is useful when we have a contradiction in the hypotheses.

For example, if we have `h : ¬ P` as a hypothesis and we apply `exfalso`
we can then `apply h` to transform the goal into `⊢ P`.

-/

/-
In Lean, the  negation `¬ P` of a statement is a shorthand for `P → false`. Therefore
-/

/- Hint : Click here for a hint, in case you get stuck.
Start with `exfalso`, and remember that negation is the same as `→ false`.
-/

variables {X Y : Type} -- hide

/- Example : no-side-bar
We can prove that 1 equals 0 if we have a contradiction in our hypotheses.
-/
example (A : set X) (x : X) (h1 : x ∈ A) (h2 : x ∉ A): 1 = 0 :=
begin
  exfalso,
  apply h2,
  exact h1,

  
end
