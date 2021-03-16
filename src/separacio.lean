import topologia

open topological_space
open set

variables (X : Type) [topological_space X]

/-- Kuratowski's problem -/
example (A : set X) : closure (interior (closure( interior A))) = closure (interior A) :=
begin
  sorry,
end

/-- Kuratowski's problem -/
example (A : set X) : interior (closure( interior (closure A))) = interior (closure A) :=
begin
  sorry,
end

def is_dense {X : Type} [topological_space X] (A : set X) : Prop := closure A = univ

lemma dense_iff (A : set X) : is_dense A ↔ (interior (A.compl) = ∅) :=
begin
  sorry
end

lemma dense_iff' (A : set X) : is_dense A ↔
  ∀ x : X, ∀ U : set X, is_neighborhood U x → U ∩ A ≠ ∅ :=
begin
  sorry
end

def boundary {X : Type} [topological_space X] (A : set X) := closure A ∩ closure Aᶜ

lemma boundary_def (A : set X) : boundary A = (closure A) \ (interior A) :=
begin
  sorry
end

lemma mem_boundary_iff (A : set X) (x : X) :
  x ∈ boundary A ↔ ∀ U : set X, is_neighborhood U x → (U ∩ A ≠ ∅ ∧ U ∩ A.compl ≠ ∅) :=
begin
  sorry
end

class kolmogorov_space : Prop :=
(t0 : ∀ (x y : X) (h : y ≠ x) , ∃ (U : set X) (hU : is_open U), ((x ∈ U) ∧ (y ∉ U)) ∨ ((x ∉ U) ∧ (y ∈ U)))

class frechet_space : Prop := 
(t1 : ∀ (x y : X) (h : y ≠ x), ∃ (U : set X) (hU : is_open U), (x ∈ U) ∧ (y ∉ U)) -- Marc : look up what's the best way to do this

namespace frechet_space

instance T1_is_T0 [frechet_space X] : kolmogorov_space X :=
{ t0 := 
begin
  intros x y hxy,
  obtain ⟨U, hU, hh⟩ := t1 x y hxy,
  use U,
  split,
  { exact hU },
  {
    left,
    exact hh,
  },
end
}

lemma T1_characterisation : frechet_space X ↔ (∀ (x : X), is_closed ({x} : set X)) :=
begin
  split,
  {
    intros h x,
    unfold is_closed,
    let I := {U : set X | (x ∉ U) ∧ (is_open U)},
    have p : ⋃₀ I = {x}ᶜ,
    {
      apply subset.antisymm; intros t ht, 
      {
        rcases ht with ⟨A,⟨hxA, hA⟩, htA⟩,
        simp,
        intro htx,
        rw htx at htA,
        exact hxA htA,     
      },
      {
        have htx := (mem_compl_singleton_iff.mp ht).symm,
        replace h := h.t1,
        obtain ⟨U, hU, hh⟩ := h t x htx,
        exact ⟨U, ⟨hh.2, hU⟩, hh.1⟩,
      }
    },
    rw ← p,
    have c : ∀ B ∈ I, is_open B,
      finish,
    exact topological_space.union I c,
  },
  {
    intros h,
    fconstructor,
    intros x y hxy,
    exact ⟨{y}ᶜ,h y, mem_compl_singleton_iff.mpr (ne.symm hxy), not_not.mpr rfl⟩,
  }
end

end frechet_space


class hausdorff_space :=
(t2 : ∀ (x y : X) (h : y ≠ x), ∃ (U V: set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), (x ∈ U) ∧ (y ∈ V))

namespace hausdorff_space

instance T2_is_T1 [hausdorff_space X] : frechet_space X :=
{ t1 := 
begin
  intros x y hxy,
  obtain ⟨U, V, hU, hV, hUV, hh⟩ := t2 x y hxy,
  rw inter_comm at hUV,
  exact ⟨U, hU, ⟨hh.1, (inter_is_not_is_empty_intersection hh.2 hUV)⟩⟩,
end }

end hausdorff_space

class T2_5_space : Prop :=
(t2_5 : ∀ (x y : X) (h : y ≠ x), ∃ (U V: set X) (hU : is_open U) (hV : is_open V) (hUV : (closure U) ∩ (closure V) = ∅), (x ∈ U) ∧ (y ∈ V))

namespace T2_5_space

instance T2_5_is_T2 [T2_5_space X] : hausdorff_space X :=
{ t2 := 
begin
  intros x y hxy,
  obtain ⟨U, V, hU, hV, hUV, hh⟩ := t2_5 x y hxy,
  have hUV₂ : U ∩ V = ∅,
  {
    apply subset.antisymm,
    {
      intros t h,
      rw ← hUV,
      exact ⟨(set_in_closure U) h.1, (set_in_closure V) h.2 ⟩, 
    },
    {
      exact (U ∩ V).empty_subset,
    },
  },
  exact ⟨U, V, hU, hV, hUV₂, hh⟩,
end } 

end T2_5_space

def is_regular := ∀ (x : X) (F : set X) (hF : is_closed F) (hxF: x ∉ F),
  ∃ (U V : set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), (x ∈ U) ∧ (F ⊆ V)

class T3_space extends frechet_space X : Prop :=
(regular : is_regular X)

namespace T3_space
open frechet_space
open hausdorff_space

instance T3_is_T2 [T3_space X] : hausdorff_space X :=
{ t2 := 
begin
  intros x y hxy,
  have H := (T1_characterisation X).1 _inst_2.to_frechet_space y,
  have x_notin_y : x ∉ ({y} : set X), by tauto,
  obtain ⟨U, V, hU, hV, hUV, hh⟩ := regular x ({y} : set X) H x_notin_y,
  rw singleton_subset_iff at hh,
  exact ⟨U, V, hU, ⟨hV, ⟨hUV, ⟨hh.1, hh.2⟩⟩⟩⟩,
end}

instance T3_is_T2_5 [T3_space X] : T2_5_space X :=
{ t2_5 := 
begin
  intros x y hxy,
  obtain ⟨U, V, hU, hV, hUV, hh⟩  := t2 x y hxy,
  have hxcV : x ∉ closure V,
  {
    rw closure_eq_compl_of_interior_compl V,
    have hxint := (@interior_is_biggest_open X _inst_1 Vᶜ U (subset_compl_iff_disjoint.mpr hUV) hU) x hh.1,
    exact not_not.mpr hxint,
  },
  obtain ⟨A, B, hA, hB, hAB, hh2 ⟩ := regular x (closure V) (closure_is_closed V) hxcV,
  have t : closure A ∩ closure V = ∅,
  {
    apply subset.antisymm,
    {
      intros t ht,
      rw ← hAB,
      split,
      {
        sorry
      },
        exact hh2.2 ht.2,
    },
      exact (closure A ∩ closure V).empty_subset,
  },
  exact ⟨A, V, hA, hV, t, hh2.1, hh.2⟩,
end }

lemma T0_and_regular_is_T3 [kolmogorov_space X] (h: is_regular X) :
  T3_space X :=
{ 
  t1 := 
  begin
    intros x y hxy,
    obtain ⟨U, hU, hh⟩ := kolmogorov_space.t0 x y hxy,
    cases hh,
      exact ⟨U, hU, hh⟩,
    {
      have hUc : is_closed Uᶜ,
      {
        simp,
        exact hU,
      },
      have hy_not_Uc : y ∉ Uᶜ,
      {
        intro t,
        exact (not_mem_of_mem_compl t) hh.2,
      },
      obtain ⟨A, B, hA, hB, hAB, hhAB⟩ := h y Uᶜ hUc hy_not_Uc,
      exact ⟨B, hB, hhAB.2 hh.1, inter_is_not_is_empty_intersection hhAB.1 hAB⟩,
    }
  end,
  regular := h,
}

lemma T0_and_regular_if_only_if_T3 : (kolmogorov_space X) ∧ (is_regular X) ↔ T3_space X :=
begin
  split; intro h,
    exact @T0_and_regular_is_T3 X _inst_1 h.1 h.2,
    exact ⟨@frechet_space.T1_is_T0 X _inst_1 (@hausdorff_space.T2_is_T1 X _inst_1 (@T3_space.T3_is_T2 X _inst_1 h)), h.regular⟩,
end

end T3_space

def is_normal (X : Type) [topological_space X] :=
  ∀ (F E : set X) (hF : is_closed F) (hE : is_closed E) (hEF : F ∩ E = ∅), 
  ∃ (U V : set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), (F ⊆ U) ∧ (E ⊆ V)

class T4_space extends frechet_space X : Prop :=
(normal : is_normal X)

namespace T4_space
open frechet_space

instance T4_is_T3 [T4_space X] : T3_space X :=
{ regular := 
begin
  intros x F hF hxF,
  obtain ⟨U, V, hU, hV, hUV, hh ⟩ := normal F {x} hF ((T1_characterisation X).1 _inst_2.to_frechet_space x)
  (inter_singleton_eq_empty.mpr hxF),
  rw inter_comm U V at hUV,
  exact ⟨V, U, hV, hU, hUV, hh.2 (mem_singleton x), hh.1⟩,
end  
}

end T4_space

class T5_space extends frechet_space X : Prop :=
(t5 : ∀ (A B : set X) (hAB : A ∩ (closure B) = ∅) (hBA : (closure A) ∩ B = ∅), ∃ (U V : set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), A ⊆ U ∧ B ⊆ V)

namespace T5_space
open frechet_space

instance T5_is_T4 [T5_space X] : T4_space X :=
{ normal := 
  begin
    intros F E hF hE hFE,
    have h₁ : (closure F) ∩ E = ∅,
      rwa ← ((eq_closure_iff_is_closed F).2 hF),
    have h₂ : F ∩ (closure E) = ∅,
      rwa ← ((eq_closure_iff_is_closed E).2 hE),
    exact t5 F E h₂ h₁,
  end}

end T5_space