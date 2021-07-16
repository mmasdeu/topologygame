import separation_world.level5 -- hide

/-
# Level 6: Characterisation of Frechet spaces
-/

variables {X : Type} -- hide
variables [topological_space X] -- hide

namespace topological_space -- hide
open set -- hide

/- Lemma
Let τ be a topological space. τ is a frechet space if only if for all the points in the topology, their singletons are closed sets.
-/
lemma T3_space.T1_space [T3_space X]: T1_space X  :=
begin
  fconstructor,
  intros x y hxy,
  obtain ⟨U, hU, hh⟩ := T0_space.t0 x y hxy,
  cases hh,
  { exact ⟨U, hU, hh⟩},
  { obtain ⟨A, B, hA, hB, hAB, hhAB⟩ := T3_space.regular y Uᶜ (by rwa [is_closed, compl_compl]) 
                                          (λ t, (not_mem_of_mem_compl t) hh.2),
    exact ⟨B, hB, hhAB.2 hh.1, (disjoint_left.1 (disjoint_iff_inter_eq_empty.2 hAB) hhAB.1)⟩}



    
  
end

end topological_space -- hide
