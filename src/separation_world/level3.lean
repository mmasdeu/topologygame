import separation_world.level2 -- hide

/-
# Level 3: Lemma about intersection of open sets
-/

variables {X : Type} -- hide
variables [topological_space X] -- hide

namespace topological_space -- hide
open set -- hide

/- Lemma
Let τ be a topological space. τ is a frechet space if only if for all the points in the topology, their singletons are closed sets.
-/
lemma union_disjont_open_sets [T1_space X] {x : X}: ⋃₀ {U : set X | (x ∉ U) ∧ (is_open U)} = {x}ᶜ :=
begin
  apply subset.antisymm; intros t ht, 
  { rcases ht with ⟨A,⟨hxA, hA⟩, htA⟩,
    rw [mem_compl_eq, mem_singleton_iff],
    rintro rfl,
    contradiction},
  { obtain ⟨U, hU, hh⟩ := T1_space.t1 t x (mem_compl_singleton_iff.mp ht).symm,
    exact ⟨U, ⟨hh.2, hU⟩, hh.1⟩},
end

end topological_space -- hide
