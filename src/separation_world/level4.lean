import separation_world.level3 -- hide

/-
# Level 4: Characterisation of Frechet spaces
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
  { introsI t1 x,
    rw [is_closed, ← union_disjont_open_sets],
    exact topological_space.union (λ B hB, hB.2)},
  { intro h, 
    exact ⟨λ x y hxy, ⟨{y}ᶜ,h y, mem_compl_singleton_iff.mpr (ne.symm hxy), not_not.mpr rfl⟩⟩}
end

end topological_space -- hide
