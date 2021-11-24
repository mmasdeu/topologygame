import data.set.basic -- hide
open set -- hide

/-
The following lemma can be proved using `ext`, `split`, `cases`, `left`, `right` tactics. 

- `ext` allows us to prove `A=B` taking an element of each set.  `x ∈ A ↔ x ∈ B`
- `split` divides the current goal `P ∧ Q` into several subgoals.#check
- `cases h` divides a combined hypothesis `h: P ∧ Q` or `h: P ∨ Q` into separated assumptions. 
- `left/right` allows us to prove `P ∨ Q` by proving either `P` or `Q`.

If you are lazy, the `finish` tactic will take the fun out of this exercise. So try to not use it.
-/

/- Hint : Click here for a hint, in case you get stuck.
Remember that `x ∈ A ∩ B` is "the same as" `x ∈ A ∧ x ∈ B`. Therefore if you have a hypothesis
of the form `h : x ∈ A ∩ B` and your goal is `⊢ x ∈ B`, you win by `exact h.2`.
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
