import data.set.basic -- hide
open set -- hide

/-
There is an equivalence between set theory and logic, and Lean identifies these two.

In this equivalence, a logic statement P : X → true/false corresponds to the set
$A = \{ x : X | P(x) \}$. Under this equivalence, logical implications P → Q translate into
set inclusions A ⊆ B, and so on.

The goal of this lemma is to prove transitivity of set inclusion, giving almost the same
proof as in the previous lemma.
-/

/- Hint : Click here for a hint, in case you get stuck.
Start with `intro x,`, then do exactly as in the previous level.
-/

variables {X Y : Type} -- hide

/- Lemma : no-side-bar
If A, B and C are sets and, and we know A ⊆ B and B ⊆ C, then
we have A ⊆ C.
-/
lemma subset_transitive (A B C : set X) (hAB : A ⊆ B) (hBC : B ⊆ C) :
  A ⊆ C :=
begin
  intro x,
  intro hA,
  apply hBC,
  apply hAB,
  exact hA,

  
end