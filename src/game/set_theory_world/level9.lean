import data.set.basic -- hide
import data.set.finite -- hide
open set -- hide
/-
We will use the following lemma when we start proving facts about topological spaces.
-/

/- Hint : Click here for a hint, in case you get stuck.

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
    have h : ⋂₀ insert U S = (⋂₀ S) ∩ U,
    {
      finish,
    },
    rw h,
    apply hinter;
    finish,
  }
end

