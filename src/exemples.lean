import .topologia
import .bases
import .productes
import .metrics
import data.real.ereal

open set
open topological_space

noncomputable theory

/- We can now work with topological spaces like this. -/
example (X : Type) [topological_space X] (U V W : set X) (hU : is_open U) (hV : is_open V)
  (hW : is_open W) : is_open (U ∩ V ∩ W) :=
begin
  apply inter _ _ _ hW,
  exact inter _ _ hU hV,
end

/- Defining a basic topology now works like so: -/
def discrete (X : Type) : topological_space X :=
{ is_open := λ U, true, -- everything is open
  univ_mem := trivial,
  union := λ _ _, by trivial,
  inter := λ _ _ _ _, by trivial }

/-- The indiscrete topology is the coarsest possible one. -/
def indiscrete (X : Type) : topological_space X := generate_from ∅

/- The union of a family of sets containing univ is univ -/
lemma sUnion_univ_of_mem_univ {X : Type} {I : set (set X)} (h : univ ∈ I) : ⋃₀ I = univ :=
begin
  rw sUnion_eq_univ_iff,
  intros x,
  use univ,
  exact ⟨h, mem_univ x⟩,
end

/-- The only opens in the indiscrete topology are ∅ and univ -/
lemma indiscrete_is_open_iff {X : Type} (U : set X) :
@is_open _ (indiscrete X) U ↔ U = ∅ ∨ U = univ :=
begin
  split,
  {
    intro h,
    induction h with _ _ I hI hI' W1 W2 hW1 hW2 hW1' hW2',
    { tauto },
    { tauto },
    {
      by_cases H : univ ∈ I,
      { exact or.inr (sUnion_univ_of_mem_univ H) },
      {
        left,
        rw sUnion_eq_empty,
        finish,
      }
    },
    {
      cases hW1',
      {
        left,
        rw [inter_comm, hW1'],
        apply inter_empty,
      },
      subst hW1',
      simpa,
    },
  },
  {
    intro h,
    cases h,
    all_goals {rw h, simp },
  }
end


/-
Show that {∅, univ, (-∞, a) : a : ℝ} is a topology on ℝ
-/
open real
open ereal

def left_ray : ereal → (set ℝ) := λ a , (ite (a = ⊥) ∅ (ite (a = ⊤) univ {x : ℝ | (x : ereal) < a}))

@[simp]
lemma left_ray_top_def : left_ray ⊤ = univ :=
begin
  unfold left_ray,
  simp,
  tauto,
end

@[simp]
lemma left_ray_bot_def : left_ray ⊥ = ∅ :=
begin
  unfold left_ray,
  simp,
end

@[simp]
lemma left_ray_eq_Iio (x : ℝ) : left_ray (x : ereal) = Iio x :=
begin
  unfold left_ray,
  have xnetop : (x : ereal) ≠ ⊤, by trivial,
  have xnebot : (x : ereal) ≠ ⊥ := dec_trivial,
  simp [xnetop, xnebot, Iio_def],
end

@[simp]
lemma left_ray_mem (x : ℝ) (y : ereal) : x ∈ left_ray y ↔ (x : ereal) < y :=
begin
  by_cases ht : y = ⊤,
  {
    simp [ht],
    exact dec_trivial,
  },
  by_cases hb : y = ⊥,
  { simp [hb] },
  obtain ⟨z, hz⟩ := lift_to_real hb ht,
  subst hz,
  simp,
end

lemma left_ray_def (x : ereal) : left_ray x = {y : ℝ | (y : ereal) < x } :=
begin
  ext,
  simp,
end

@[simp]
lemma left_ray_univ_iff (b : ereal) : left_ray b = univ ↔ b = ⊤ :=
begin
  split,
  {
    intro h,
    unfold left_ray at h,
    by_contradiction hc,
    simp [hc] at h,
    by_cases ht : b = ⊥,
    {
      subst ht,
      simp at h,
      exact empty_ne_univ h,
    },
    obtain ⟨z, hz⟩ := lift_to_real ht hc,
    simp [ht] at h,
    subst hz,
    simp at h,
    specialize h (z+1),
    linarith [h],
  },
  exact λ h, by simp [h],
end

@[simp]
lemma left_ray_empty_iff (b : ereal) : left_ray b = ∅ ↔ b = ⊥ :=
begin
  split,
  {
    intro h,
    unfold left_ray at h,
    by_contradiction hc,
    simp [hc] at h,
    by_cases ht : b = ⊤,
    { simpa [ht] using h },
    { simp [ht] at h,
      obtain ⟨z, hz⟩ := lift_to_real hc ht,
      subst hz,
      simp at h,
      specialize h (z-1),
      linarith [h] },
  },
  exact λ h, by simp [h],
end

@[simp]
lemma left_ray_subset_iff (a b : ereal) : left_ray a ⊆ left_ray b ↔ a ≤ b :=
begin
  by_cases ha1 : a = ⊥,
  { simp [ha1] },
  by_cases ha2 : a = ⊤,
  { simp [ha2, univ_subset_iff] },
  by_cases hb1 : b = ⊥,
  { simp [hb1, subset_empty_iff] },
  by_cases hb2 : b = ⊤,
  { simp [hb2] },
  { simp [left_ray_def],
    obtain ⟨r, hr⟩ := lift_to_real ha1 ha2,
    obtain ⟨s, hs⟩ := lift_to_real hb1 hb2,
    subst hr, subst hs,
    simp,
    exact forall_lt_iff_le },
end

@[simp]
lemma left_ray_inter (a b : ereal) :
  left_ray a ∩ left_ray b = left_ray (min a b) :=
begin
  by_cases a ≤ b,
  {
    rw min_eq_left h,
    apply inter_eq_self_of_subset_left,
    simp [h],
  },
  {
    push_neg at h,
    replace h := le_of_lt h,
    rw min_eq_right h,
    apply inter_eq_self_of_subset_right,
    simp [h],
  }
end

lemma union_of_intervals {α : set ℝ} (hne : ∃ a : ℝ, a ∈ α) (h : ∃ (C : ℝ), ∀ a ∈ α, a ≤ C) :
  (⋃ a ∈ α, Iio a) = Iio (Sup α) :=
begin
  simp only [←Iio_def],
  ext,
  simp [lt_Sup α hne h],
end

lemma bUnion_left_ray {α : set ereal} :
  (⋃ a ∈ α, left_ray a) = left_ray (Sup α) :=
begin
  apply eq_of_subset_of_subset,
  {
    apply bUnion_subset,
    exact λ _ hx, by simp [ereal.le_Sup hx],
  },
  {
    intros x hx,
    rw mem_bUnion_iff,
    have hx' : (x : ereal) < Sup α, by simpa using hx,
    obtain ⟨y, ⟨hy1, hy2⟩⟩ := ereal.lt_Sup hx',
    exact ⟨y, by simp [hy1, hy2]⟩,
  }
end

def left_ray_topology : topological_space ℝ := {
  is_open := left_ray '' univ,
  univ_mem := ⟨⊤, by tauto⟩,
  union :=
  begin
    intros Y hY,
    use Sup (left_ray⁻¹' Y),
    simp [←bUnion_left_ray, sUnion_eq_bUnion],
    ext1,
    simp,
    split,
    { rintro ⟨a, ha⟩,
      exact ⟨left_ray a, by simp [ha]⟩ },
    {
      rintro ⟨B, hB⟩,
      obtain ⟨i, ⟨hi1, hi2⟩⟩ := hY B hB.1,
      use i,
      rw [←left_ray_mem, hi2],
      exact hB,
    }
  end,
  inter :=
  begin
    rintros A B ⟨a, _, haA⟩ ⟨b, _, hbB⟩,
    subst haA, subst hbB,
    exact ⟨min a b, by simp⟩,
  end
}

/-
Define the family of intervals of the form [a, b)
-/
def Icos := {B : set ℝ | ∃ a b : ℝ, B = Ico a b }

example : basis_condition Icos :=
begin
  split,
  {
    ext,
    split,
    {
      intro h,
      fconstructor,
      use Ico (x - 1) (x + 1),
      norm_num,
      use x-1,
      use x+1,     
    },
    {
      intro h,
      trivial,
    },
  },
  {
    intros U V hU hV x,
    rcases hU with ⟨Ua, ⟨Ub , Uab_h⟩⟩,
    rcases hV with ⟨Va, ⟨Vb , Vab_h⟩⟩,
    intro hx,
    use Ico (max Ua Va) (min Ub Vb),
    split,
    {
      unfold Icos,
      use max Ua Va,
      use min Ub Vb,
    },
    {
    split,
    {
      unfold Ico,
      split;
        finish,
    },
    {
      unfold Ico,
      norm_num,
      split,
      {
        subst U,
        intros a ha,
        finish,
      },
      {
        intros a ha,
        subst V,
        finish,
      },
    },
  },
},
end

-- definir una topologia per un conjunt de tres elements