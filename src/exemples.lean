import .topologia
import .bases
import .productes
import .metrics

open set
open topological_space

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
      {
        right,
        rw sUnion_eq_univ_iff,
        intros x,
        use univ,
        exact ⟨H, mem_univ x⟩,
      },
      {
        left,
        suffices : ∀ t ∈ I, t = ∅, by simpa [sUnion_eq_empty] using this,
        intros t ht,
        specialize hI' t ht,
        cases hI',
        { exact hI' },
        {
          rw hI' at ht,
          contradiction,
        }
      }
    },
    {
      cases hW1',
      {
        left,
        rw [inter_comm, hW1'],
        apply inter_empty,
      },
      cases hW2',
      {
        left,
        rw hW2',
        apply inter_empty,
      },
      {
        right,
        rw [hW1',hW2'],
        apply inter_univ,
      },
    },
  },
  {
    intro h,
    cases h,
    { 
      rw h,
      exact @empty_mem _ (indiscrete X),
    },
    {
      rw h,
      exact @univ_mem _ (indiscrete X),
    }
  }
end


/-
Show that {∅, univ, (-∞, a) : a : ℝ} is a topology on ℝ
-/
open real

lemma union_of_intervals {α : set ℝ} (hne : ∃ a : ℝ, a ∈ α) (h : ∃ (C : ℝ), ∀ a ∈ α, a ≤ C) :
  (⋃ a ∈ α, Iio a) = Iio (Sup α) :=
begin
  simp only [←Iio_def],
  ext,
  simp [lt_Sup α hne h],
end

def left_ray_topology : topological_space ℝ := {
  is_open := λ (X : set ℝ),  X = ∅ ∨ X = univ ∨ (∃ a : ℝ, X = Iio a),
  univ_mem := by tauto,
  union := 
  begin
    intro I,
    intro h,
    by_cases hempty : ∀ B ∈ I, B = ∅,
    {
      left,
      simp,
      exact hempty,
    },
    push_neg at hempty,
    right,
    by_cases huniv : ∃ B ∈ I, B = univ,
    {
      left,
      simp at *,
      ext1,
      norm_num,
      use univ,
      exact ⟨huniv, mem_univ x⟩,
    },
    push_neg at huniv,
    let α := {a | ∃ B ∈ I, B = Iio a},
    have hαne : ∃ a : ℝ, a ∈ α,
    {
      simp*,
      cases hempty with T hT,
      specialize h T hT.1,
      rcases h with h1 | h2 | h3,
      {
        by_contradiction,
        exact hT.2 h1,
      },
      {
        by_contradiction,
        exact (huniv T hT.1) h2,
      },
      {
        cases h3 with a ha,
        use a,
        rw ← ha, 
        exact hT.1,
      },
    },
    by_cases hbounded : ∃ c : ℝ, ∀ a ∈ α, a ≤ c,
    {
      right,
      use Sup α,
      rw ←union_of_intervals hαne hbounded,
      {
        dsimp,
        ext1,
        dsimp,
        split,
        {
          intro hx,
          simp,
          obtain ⟨B, ⟨hBI, hxB⟩⟩ := hx,
          specialize h B hBI,
          replace h : ∃ (a : ℝ), B = Iio a,
          {
            rcases h with h1 | h2 | h3;
            finish,
          },
          obtain ⟨a, ha⟩ := h,
          use a,
          rw ←ha,
          finish,
        },
        intro hx,
        simp at hx,
        obtain ⟨a, ha⟩ := hx,
        use Iio a,
        simpa using ha,
      },
    },
    push_neg at hbounded,
    left,
    ext,
    simp only [exists_prop, mem_univ, mem_set_of_eq, iff_true],
    obtain ⟨a, ⟨ha1, ha2⟩⟩ := hbounded x,
    use Iio a,
    split; finish,
  end,
  inter :=
  begin
    intros A B,
    intros hA hB,
    rcases hA with hA  | hA | hA,
    {
      left,
      subst hA,
      exact empty_inter B,
    },
    {
      subst hA,
      simp,
      exact hB,
    },
    {
      rcases hB with hB  | hB | hB,
      {
        left,
        subst hB,
        exact inter_empty A,
      },
      {
        subst B,
        simp,
        right,right,
        exact hA,
      },
      {
        obtain ⟨a, ha⟩ := hA,
        subst ha,
        obtain ⟨b, hb⟩ := hB,
        subst hb,
        right,right,
        use min a b,
        exact Iio_inter_Iio,
      },
    }
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
