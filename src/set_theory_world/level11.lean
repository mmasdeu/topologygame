import data.set.basic -- hide
open set -- hide

variables {X Y : Type} -- hide

/- Lemma : no-side-bar
Giving an element `p` of a product type `X × Y` and two subsets `A ⊆ X` `B ⊆ Y`. The element 
`p` is the set `A × B` (as sets) if only if the first component of `p` is in `A` and the second in `B`.
-/
lemma sInter_of_inter {p : X × Y} (A: set X) (B : set Y): p ∈ A.prod B ↔ p.1 ∈ A ∧ p.2 ∈ B :=
begin
  split;
  intro h;
  exact ⟨h.1, h.2⟩
end