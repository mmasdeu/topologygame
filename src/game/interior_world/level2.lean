import game.interior_world.definition -- hide


/-

# Level 2: Second definition of the interior

Before we keep proving properties of the iterior of an arbitrary set, we will prove an alternative definition of it.

-/
variables {X : Type} -- hide
variables [topological_space X] (x : X)  (A : set X) -- hide

namespace topological_space -- hide


/- Lemma
The interior of a set A is the union of all the open sets that it contains:
$ \operatorname{int}(A) = \bigcup_{U \subseteq A, U\text{ open}} U$
-/
lemma interior_def' : interior A = ⋃₀ {U : set X | is_open U ∧ U ⊆ A} :=
begin
  ext,
  split,
  {
    rintros ⟨U, is_open_U, x_in_U, U_subset_A⟩,
    use U,
    exact ⟨⟨is_open_U, U_subset_A⟩, x_in_U⟩,
  },
  {
    rintros ⟨U, ⟨is_open_U, U_subset_A⟩, x_in_U⟩,
    use U,
    exact ⟨is_open_U, ⟨x_in_U, U_subset_A⟩⟩
  },







end

end topological_space -- hide