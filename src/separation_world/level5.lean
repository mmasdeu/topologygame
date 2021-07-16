import separation_world.level4 -- hide

/-
# Level 5: Every T₂ space is also T₁
-/

variables {X : Type} -- hide
variables [topological_space X] -- hide

namespace topological_space -- hide
open set -- hide

/- Lemma
Let τ be a topological space. τ is a frechet space if only if for all the points in the topology, their singletons are closed sets.
-/
lemma T2_space.T1_space [T2_space X]: T1_space X  :=
begin
  exact {t1 := λ x y hxy, let ⟨U, V, hU, hV, hUV, hh⟩  := T2_space.t2 x y hxy in 
          ⟨U, hU, hh.1, not.imp (not_not.mpr hh.2) (λ c, (subset_compl_iff_disjoint.2 hUV) c)⟩ }




          
end

end topological_space -- hide
