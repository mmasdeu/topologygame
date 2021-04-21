import data.set.basic --
open set
/-
The following lemma can be proved using `ext`, `split`, `cases`, `left`, `right` tactics.
-/

/- Hint : Click here for a hint, in case you get stuck.

-/

variables {X Y : Type} -- hide

/- Lemma : no-side-bar
The distributive property of ∩ with respect to ∪.
-/
lemma inter_union (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext,
  split,
  {
    intro h,
    cases h,
    cases h_right,
    {
      left,
      split;
      assumption,
    },
    {
      right,
      split;
      assumption,
    }
  },
  {
    intro h,
    cases h,
    {
      split,
      {
        exact h.1,
      },
      {
        left,
        exact h.2,
      },
    },
    {
      split,
      {
        exact h.1,
      },
      {
        right,
        exact h.2,
      }
    }
  }
end
