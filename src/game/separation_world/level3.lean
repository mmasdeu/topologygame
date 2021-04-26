import game.separation_world.level2 -- hide

/-
# Level 3: Characterisation of Frechet spaces
-/

variables {X : Type} -- hide
variables [topological_space X] -- hide

namespace topological_space -- hide
open set -- hide

/- Lemma
Let τ be a topological space. τ is a frechet space if only if for all the points in the topology, their singletons are closed sets.
-/
lemma T1_characterisation : T1_space X ↔ (∀ (x : X), is_closed ({x} : set X)) :=
begin
  split,
  { introI t1, intro x,
    unfold is_closed,
    let I := {U : set X | (x ∉ U) ∧ (is_open U)},
    have p : ⋃₀ I = {x}ᶜ,
    { apply subset.antisymm; intros t ht, 
      { rcases ht with ⟨A,⟨hxA, hA⟩, htA⟩,
        rw [mem_compl_eq, mem_singleton_iff],
        intro htx,
        subst htx,
        exact hxA htA},
      { obtain ⟨U, hU, hh⟩ := T1_space.t1 t x (mem_compl_singleton_iff.mp ht).symm,
        exact ⟨U, ⟨hh.2, hU⟩, hh.1⟩}},
    rw ← p,
    exact topological_space.union I (λ B hB, hB.2)},
  { intro h, 
    exact ⟨λ x y hxy, ⟨{y}ᶜ,h y, mem_compl_singleton_iff.mpr (ne.symm hxy), not_not.mpr rfl⟩⟩}
end

end topological_space -- hide
