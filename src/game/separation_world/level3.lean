import game.basic_defs_world.definition -- hide
import game.interior_world.definition -- hide
import game.separation_world.definition -- hide

/-
# Level 3: Characterisation of Frechet spaces
-/

variables {X : Type} -- hide
variables [topological_space X] -- hide

namespace topological_space -- hide

/- Lemma
Let τ be a topological space. τ is a frechet space if only if for all the points in the topology, their singletons are closed sets.
-/
lemma T1_characterisation : T1_space X ↔ (∀ (x : X), is_closed ({x} : set X)) :=
begin
  split,
  { intros h x,
    unfold is_closed,
    let I := {U : set X | (x ∉ U) ∧ (is_open U)},
    have p : ⋃₀ I = {x}ᶜ,
    { apply subset.antisymm; intros t ht, 
      { rcases ht with ⟨A,⟨hxA, hA⟩, htA⟩,
        simp,
        intro htx,
        rw htx at htA,
        exact hxA htA},
      { have htx := (mem_compl_singleton_iff.mp ht).symm,
        replace h := h.t1,
        obtain ⟨U, hU, hh⟩ := h t x htx,
        exact ⟨U, ⟨hh.2, hU⟩, hh.1⟩}},
    rw ← p,
    have c : ∀ B ∈ I, is_open B, by finish,
    exact topological_space.union I c},
  { intros h,
    fconstructor,
    intros x y hxy,
    exact ⟨{y}ᶜ,h y, mem_compl_singleton_iff.mpr (ne.symm hxy), not_not.mpr rfl⟩}
end

end topological_space -- hide