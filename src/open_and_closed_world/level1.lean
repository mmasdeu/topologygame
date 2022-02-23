import interior_world.level5 --hide



/-

# Level 2: Second definition of the interior

Before we keep proving properties of the iterior of an arbitrary set, we will prove an alternative definition of it.

-/
variables {X : Type} -- hide
variables [topological_space X] (x : X)  (A : set X) -- hide
open set --hide
namespace topological_space -- hide


/- Lemma
The interior of a set A is the union of all the open sets that it contains:
$ \operatorname{int}(A) = \bigcup_{U \subseteq A, U\text{ open}} U$
-/
lemma open_iff_eq_closure : is_open A ↔ interior A = A :=
begin
  split; intro h,
  {
    apply subset.antisymm,
    {
      exact interior_is_subset A
    },
    {
      rw interior_def',
      intros x hx,
      exact ⟨A, ⟨h, rfl.subset⟩, hx⟩
    }
  },
  {
    rw ← h,
    exact interior_is_open A
  }


end

end topological_space -- hide
