import separation_world.level1 -- hide

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
  split; introI h,
  { fconstructor,
    intros x y hxy,
    obtain ⟨U, hU, hhU⟩ := T1_space.t1 x y hxy,
    obtain ⟨V, hV, hhV⟩ := T1_space.t1 y x (ne.symm hxy),
    exact ⟨U, V, hU, hV, hhU.1, hhU.2, hhV.2, hhV.1⟩},
  { fconstructor,
    intros x y hxy,
    obtain ⟨U, V, hU, hV, hh⟩ := T1_space'.t1 x y hxy,
    exact ⟨U, hU, ⟨hh.1,hh.2.1⟩⟩},




end


end topological_space -- hide
