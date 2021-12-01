import data.set.basic -- hide
open set -- hide

/- Tactic : ext

## Summary

If `A` and `B` are sets and the goal is `A = B`, then
using the `ext` tactic will change it to `x ∈ A ↔ x ∈ B`.

Variant: `ext y` will change the goal to `y ∈ A ↔ y ∈ B`.

## Details

This tactic applies the "extensionality" axiom of set theory,
which says that two sets are equal iff for all `x`, `x` belongs
to the first iff `x` belongs to the second.

### Example:
If it looks like this in the top right hand box:
```
A B : set X
⊢ A = B
```

then

`ext,`

will change the goal into
```
A B : set X
x : X
⊢ x ∈ A ↔ x ∈ B
```

/-
The following lemma can be proved using `ext`, `split`, `cases`, `left`, `right` tactics. 

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
/- hint
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
  sorry,
}
-/
end
