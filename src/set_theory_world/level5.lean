/- Tactic : intro

## Summary:

`intro p` will turn a goal `⊢ P → Q` into a hypothesis `p : P`
and goal `⊢ Q`. If `P` and `Q` are sets `intro p` means "let $p$ be an arbitrary element of $P$".
If `P` and `Q` are propositions then `intro p` says "assume $P$ is true". 

## Details

If your goal is a function or an implication `⊢ P → Q` then `intro`
will always make progress. `intro p` turns

`⊢ P → Q`

into 

```
p : P
⊢ Q
```

The opposite tactic to intro is `revert`; given the situation
just above, `revert p` turns the goal back into `⊢ P → Q`.

**Variant:** Instead of calling `intro` multiple times, you can use
`intros`. That is, `intros h₁ h₂` is equivalent to `intro h₁, intro h₂`.

## Example

If your goal is an implication $P\implies Q$ then Lean writes
this as `⊢ P → Q`, and `intro p,` can be thought of as meaning
"let $p$ be a proof of $P$", or more informally "let's assume that
$P$ is true". The goal changes to `⊢ Q` and the hypothesis `p : P`
appears in the local context.

-/

/-
In this level we introduce the tactic `intro`. You will need it to get started.
-/

/- Hint : Click here for a hint, in case you get stuck.
Try something like `intro h1,` and go from there.
-/

variables {X : Type} -- hide

/- Lemma : no-side-bar
If A, B and C are sets and A = B, then A ∪ C = B ∪ C.
-/
lemma example_on_intro (A B : set X) (x : X) (h : A = B) : x ∈ A → x ∈ B :=
begin
  intro h1,
  rw ← h,
  exact h1,
  
  
end

