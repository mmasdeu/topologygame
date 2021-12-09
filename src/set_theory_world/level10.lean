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
-/


/- Tactic : left and right

## Summary

`left` and `right` work on the goal, and they change
`⊢ P ∨ Q` to `⊢ P` and `⊢ Q` respectively.

## Details

The tactics `left` and `right` work on a goal which is a type with
two constructors, the classic example being `P ∨ Q`. 
To prove `P ∨ Q` it suffices to either prove `P` or prove `Q`,
and once you know which one you are going for you can change
the goal with `left` or `right` to the appropriate choice.
-/

/- Tactic : cases

## Summary:

`cases` is a tactic which works on hypotheses.
If `h : P ∧ Q` or `h : P ↔ Q` is a hypothesis then `cases h with h1 h2` will remove `h`
from the list of hypotheses and replace it with the "ingredients" of `h`,
i.e. `h1 : P` and `h2 : Q`, or `h1 : P → Q` and `h2 : Q → P`. Also
works with `h : P ∨ Q` and `n : mynat`. 

## Details

How does one prove `P ∧ Q`? The way to do it is to prove `P` and to
prove `Q`. There are hence two ingredients which go into a proof of
`P ∧ Q`, and the `cases` tactic extracts them. 

More precisely, if the local context contains
```
h : P ∧ Q`
```

then after the tactic `cases h with p q,` the local context will
change to
```
p : P,
q : Q
```
and `h` will disappear. 

Similarly `h : P ↔ Q` is proved by proving `P → Q` and `Q → P`,
and `cases h with hpq hqp` will delete our assumption `h` and
replace it with
```
hpq : P → Q,
hqp : Q → P
```

Be warned though -- `rw h` works with `h : P ↔ Q` (`rw` works with
`=` and `↔`), whereas you cannot rewrite with an implication.

`cases` also works with hypotheses of the form `P ∨ Q`. Here the situation
is different however. 
To prove `P ∨ Q` you need to give either a proof of `P` *or* a proof
of `Q`, so if `h : P ∨ Q` then `cases h with p q` will change one goal
into two, one with `p : P` and the other with `q : Q`.
-/


/-
The following lemma can be proved using `ext`, `split`, `cases`, `left`, `right` tactics. Learn what
they do in the side-bar, and use them to clear this goal.

If you are lazy, the `finish` tactic will take the fun out of this exercise. So try to not use it.
-/

variables {X Y : Type} -- hide

/- Lemma :
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
