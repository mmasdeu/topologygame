import data.set.basic -- hide
import data.set.finite -- hide
open set -- hide
/-
We will use the following lemma when we start proving facts about topological spaces.

It seems clear that we want to use induction, so we can try to apply the `finite.induction_on`
lemma. But be careful on how you apply it, or you will be left with an impossible goal.

For the inductive step, the lemmas `sInter_insert`, `mem_insert_iff` and `forall_eq_or_imp`
may be useful, as well as the `simp` tactic.
-/

/- Hint : Click here for a hint, in case you get stuck.
The `finite.induction_on` lemma allows to prove something of the form `P S` for all finite sets `S`.
So apply `finite.induction_on hfin` looks like it's making progress. However, the induction
hypothesis you will be left with is too weak. Try instead starting with `revert hS`, and
see why this helps.
-/

variables {X Y : Type} -- hide

/- Lemma : no-side-bar
If P is a property of sets which is closed under pairwise intersection then it is also closed under
arbitrary finite interesctions.
-/
lemma sInter_of_inter (P : set X → Prop) (huniv : P univ) (hinter : ∀ A B : set X, P A → P B → P (A ∩ B))
(S : set (set X)) (hfin : finite S) (hS : ∀ s ∈ S, P s) : P ( sInter S ) :=
begin
  revert hS,
  apply finite.induction_on hfin,
  { 
    simp,
    exact huniv,
  },
  {
    intros U S hUS hSfin hind h,
    have h : ⋂₀ insert U S = (⋂₀ S) ∩ U, by finish,
    rw h,
    apply hinter;
    finish,
  }
end

