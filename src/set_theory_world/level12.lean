import data.set.basic -- hide
import data.set.finite -- hide
open set -- hide

/- Tactic : use
-/

/- Lemma : If A and B are sets, then there exists a set S such that S ⊆ A ∩ B.

-/
lemma example_on_use (α : Type) (A : set α) (B : set α) : ∃ S : set α, S ⊆ A ∩ B :=
begin
  use ∅,
  intros h h1,
  split,
  repeat{
    exfalso,
    exact h1,
  },





end
