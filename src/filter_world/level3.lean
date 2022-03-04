import filter_world.level2 --hide
open set --hide
namespace filters --hide
localized "notation `P` := principal" in filters --hide

/-
# Level 3: The bottom filter
-/

/- Lemma
There exists a bottom filter among the filters of a given set.
-/
lemma top_bottom_filters {X : Type}: ∃ (B T : filter X), ∀ (F : filter X), B ≤ F ∧ F ≤ T :=
begin
  use P ∅,
  use P univ,
  intro F,
  split,
  {
    intros A hA,
    have h_emp : (∅ : set X) ∈ P (∅ : set X),
    { rw mem_principal },
    have h_emp_A : (∅ : set X) ⊆ A,
    { exact empty_subset A },
    exact filter.sets_of_superset (P ∅) h_emp h_emp_A
  },
  {
    intros A hA,
    obtain h_uni := (univ_filter_univ A).1 hA,
    rw h_uni,
    exact filter.univ_sets F
  }

end

end filters --hide
