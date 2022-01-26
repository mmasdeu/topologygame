/- Tactic : rw / rwa

## Summary

If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s. 

**Variants:** `rw ← h` changes
`Y` to `X` and
`rw h at h2` changes `X` to `Y` in hypothesis `h2` instead
of the goal.

**Variant (rw and assumption):** If instead you use `rwa h` or `rwa ← h`, Lean does performs
the `rw` and then looks whether
the goal is exactly one of your assumptions, in which case it closes it.

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

**Important note:** if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw h` will work.

**Pro tip 1:** If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l`,
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:
```
A B C : set X
h : A = B ∪ C
⊢ A ∪ B = B ∪ C
```

then

`rw h,`

will change the goal into `⊢ B ∪ C ∪ B = B ∪ C`.

### Example: 
You can use `rw` to change a hypothesis as well. 
For example, if your local context looks like this:
```
A B C D : set X
h1 : A = B ∩ C
h2 : B ∪ A = D
⊢ D = B
```
then `rw h1 at h2` will turn `h2` into `h2 : B ∪ B ∩ C = D` (remember operator precedence).

-/


/-
The next tactic we will learn is *rw* (from rewrite). It rewrites equalities. That is,
if we have a proof `h : A = B` and we want to prove `⊢ A ∩ C = B ∩ C`, then after `rw h` the goal
will become `⊢ A ∩ C = A ∩ C`, which seems reasonable.

After many tactics (and `rw` is one of them) Lean tries to apply `refl`. This is why
in the following proof you may get away with only one tactic application.

-/

/- Hint : Click here for a hint, in case you get stuck.
Delete `sorry` and type `rw h,` (don't forget the comma!). Lean tries `refl` afterwards,
so you will see that this suffices.
-/

variables {X : Type} -- hide

/- Lemma : no-side-bar
If A, B and C are sets and A = B, then A ∪ C = B ∪ C.
-/
lemma union_eq (A B C: set X) (h : A = B) : A ∪ C = B ∪ C :=
begin
  rw h,
  
end
