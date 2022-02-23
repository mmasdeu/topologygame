import data.set.basic -- hide
import data.set.finite -- hide
open set -- hide

/- Tactic : use

## Summary
The tactic use specializes the goal with a particular case. For example, if we want to prove the statement "there exists a natural number which is odd", we will need to provide a concrete number like 3. 

-/

/- Lemma :
If A and B are subsets of a fixed set, then there exists a subset S such that S ⊆ A ∩ B.
-/
lemma example_on_use (α : Type) (A : set α) (B : set α) : ∃ S : set α, S ⊆ A ∩ B :=
begin
  use ∅,
  intros h h1,
  split,
  repeat
  {
    exfalso,
    exact h1
  }

end
