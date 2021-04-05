import game.basic_defs_world.definition -- hide
import game.interior_world.definition -- hide
import game.separation_world.definition -- hide

/-
# Level 2: Comparison between the definition given and common definition of T₁
-/

variables {X : Type} -- hide
variables [topological_space X] -- hide

namespace topological_space -- hide


/- Lemma
The definitions T1_space and T1_space' are equivalent.
-/
lemma T1_space_iff_T1_space' : T1_space X ↔ T1_space' X:=
begin
  split; intro h,
  { fconstructor,
    intros x y hxy,
    obtain ht1 := h.t1,
    obtain ⟨U, hU, hhU⟩ := ht1 x y hxy,
    obtain ⟨V, hV, hhV⟩ := ht1 y x (ne.symm hxy),
    exact ⟨U, V, hU, hV, hhU.1, hhU.2, hhV.2, hhV.1⟩},
  { fconstructor,
    intros x y hxy,
    obtain ht1' := h.t1,
    obtain ⟨U, V, hU, hV, hh⟩ := ht1' x y hxy,
    exact ⟨U, hU, ⟨hh.1,hh.2.1⟩⟩},




end


end topological_space -- hide