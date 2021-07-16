import interior_world.level4 --hide
/-

# Level 5: Characterization of the interior



-/
variables {X : Type} -- hide
variables [topological_space X] (x : X)  (A B : set X) -- hide

namespace topological_space -- hide

/- Lemma
The interior of a set A is the biggest subset satisfying:
 - It is contained in A
 - It is open.
-/
lemma interior_def'': is_open B ∧ B ⊆ A ∧ (∀ U, U ⊆ A → is_open U → U ⊆ B) ↔ B = interior A :=   
begin
  split,
  {
    rintros ⟨is_open_B, ⟨B_subset_A, B_is_biggest_open⟩⟩,
    ext1,
    split,
    {
      apply interior_maximal A B B_subset_A is_open_B,
    },
    {
      intro ha,
      exact B_is_biggest_open (interior A) (interior_is_subset A) (interior_is_open A) ha,
    },
  },
  {
    intro,
    subst B,
    exact ⟨interior_is_open A, ⟨interior_is_subset A, interior_maximal A⟩⟩,
  },











end 

end topological_space -- hide
