import filter_world.level1 --hide

open set --hide
namespace filters --hide
localized "notation `P` := principal" in filters --hide

lemma mem_principal {X : Type} {s t : set X} : s ∈ P t ↔ t ⊆ s := iff.rfl -- hide

/- Axiom :
mem_principal : s ∈ P t ↔ t ⊆ s
-/

/-
# Level 2: Characterization of the princial filter of the total set
-/

/- Lemma
The only element of the principal filter of the universal set is the universal set.
-/
lemma univ_filter_univ {X : Type}: ∀ (A : set X), A ∈ P (univ : set X) ↔ A = univ :=
begin
  intros A,
  split; intro hA,
  {
    rw mem_principal at hA,
    ext,
    split,
    { intro hx,
      exact mem_univ x },
    { intro hx,
      exact hA hx }
  },
  {
    rw mem_principal,
    rw hA
  }


end

end filters --hide
