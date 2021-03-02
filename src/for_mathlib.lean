
import data.real.ereal

open set

noncomputable theory


@[simp]
lemma set.univ_iff {α : Type} {p : α → Prop} : {x : α | p x} = univ ↔ ∀ x, p x :=
begin
  split,
  {
    intros h x,
    have h1 := mem_univ x,
    rw ← h at h1,
    exact h1,
  },
  {
    intros h,
    ext,
    simp,
    exact h x,
  }
end

@[simp]
lemma set.empty_iff {α : Type} {p : α → Prop} : {x : α | p x} = ∅ ↔ ∀ x, ¬ p x :=
begin
  split,
  {
    intros h x,
    have h1 := mem_empty_eq x,
    rw ← h at h1,
    simpa using h1,
  },
  {
    intros h,
    ext,
    simp,
    exact h x,
  }
end


lemma lift_to_real {x : ereal} (h : x ≠ ⊥) (h' : x ≠ ⊤) :
  ∃ (c : ℝ), (c : ereal) = x :=
begin
  cases x,
  { tauto },
  cases x,
  { tauto },
  use x,
  tauto,
end

instance complete_linear_order_ereal : complete_linear_order ereal :=
{ ..ereal.complete_lattice, ..ereal.linear_order }

lemma ereal.le_Sup {α : set ereal} {x : ereal} (h : x ∈ α) : x ≤ Sup α :=
  @_root_.le_Sup ereal _ _ _ h

lemma ereal.lt_Sup {α : set ereal} {x : ereal} (h : x < Sup α) : ∃ y ∈ α, x < y :=
  (@_root_.lt_Sup_iff ereal _ α x).1 h

lemma ereal_top (x : ereal) (h : ∀ (y : ℝ), (y : ereal) < x) : x = ⊤ :=
begin
  by_contradiction hc,
  by_cases hb : x = ⊥,
  {
    subst hb,
    finish,
  },
  obtain ⟨z, hz⟩ := lift_to_real hb hc,
  specialize h z,
  rw hz at h,
  finish,
end

lemma ereal_bot (x : ereal) (h : ∀ (y : ℝ), x < (y : ereal)) : x = ⊥ :=
begin
  by_contradiction hc,
  by_cases ht : x = ⊤,
  {
    subst ht,
    finish,
  },
  obtain ⟨z, hz⟩ := lift_to_real hc ht,
  specialize h z,
  rw hz at h,
  finish,
end
