import topology.constructions
import topology.separation
import topology.basic 
import for_mathlib
import topology.metric_space.basic

open set

lemma bolz (a b : ℝ) (hab : a < b) (f: ℝ → ℝ) (hf : continuous_on f (Icc a b)) (ha : (f a)<0 ∧ (f b)>0) : ∃ c ∈ (Icc a b),f(c)=0 :=
begin
  have h1 : ∃ (x : ℝ), x ∈ {x ∈ Icc a b | f x ≥ 0}, 
  { exact ⟨b, right_mem_Icc.2 (le_of_lt hab), ge_iff_le.1 (le_of_lt ha.2)⟩ },
  have hb : Inf {x ∈ Icc a b | f x ≥ 0} ≤ b,
  { exact real.Inf_le {x ∈ Icc a b | f x ≥ 0} ⟨a, (λ y hy, (mem_Icc.1 hy.1).1)⟩ ⟨right_mem_Icc.2 (le_of_lt hab), ge_iff_le.2 (le_of_lt ha.2)⟩ },
  let I := {x ∈ Icc a b | f x ≥ 0},
  cases ha with ha1 ha2,
  have hclosu : ∀ x ∈ closure I , 0 ≤ (f x),
  {
    sorry
  },
  have himI : 0 ≤ f (Inf I),
  {
    have h : Inf I ∈ closure I,
    {
      
      sorry
    },
    exact hclosu (Inf I) h,
  },
  have ha : a < Inf {x ∈ Icc a b | f x ≥ 0},
  { have h3 : a ≠ Inf I,
    { intro hax,
      have htt : f (Inf I) <0, by rwa ← hax,
      linarith },
    exact (ne.le_iff_lt h3).mp ((real.le_Inf {x ∈ Icc a b | f x ≥ 0} h1 ⟨a, (λ y hy, (mem_Icc.1 hy.1).1)⟩).2 (λ x hx, (mem_Icc.1 hx.1).1)) },
  have hI :=  mem_Icc.mpr ⟨(real.le_Inf {x ∈ (Icc a b)| f x >= 0} h1 ⟨a, (λ y hy, (mem_Icc.1 hy.1).1)⟩).2 (λ y hy, (mem_Icc.1 hy.1).1), hb⟩,
  have hf : f (Inf {x ∈ Icc a b | f x ≥ 0}) = 0,
  { by_contradiction,
    cases (ne.symm h).lt_or_lt,
    { obtain ⟨δ₀, hδ₀ , hh⟩  := metric.continuous_on_iff.1 hf (Inf I) hI ((f (Inf I))/2) (half_pos h_1),
      let δ := min δ₀ ((Inf I)-a),
      have hδ : δ > 0,
      { exact lt_min hδ₀ (by linarith) },
      have hhδ : ∀ (a_1 : ℝ), a_1 ∈ Icc a b → dist a_1 (Inf I) < δ → dist (f a_1) (f (Inf I)) < f (Inf I) / 2,
      { intros x hx hxd,
        exact hh x hx (by linarith[min_le_left δ₀ (Inf I - a)]) },
      have t : Inf I - δ/2 ∈ Icc a b,
      { exact (mem_Icc.mpr ⟨by linarith [min_le_right δ₀ ((Inf I)-a)], by linarith⟩) },
      have tt : dist (Inf I - δ/2) (Inf I) < δ,
      { have m : abs(Inf I - δ/2 - Inf I) = δ/2,
        { ring_nf,
          rw abs_neg,
          exact abs_of_pos (by linarith) },
        rw [real.dist_eq (Inf I - δ/2) (Inf I), m],
        linarith },
      obtain hhh := (hhδ (Inf I - δ/2) t tt),
      have r : 0 < f (Inf I - δ/2),
      { rw real.dist_eq at hhh,
        linarith[neg_lt_of_abs_lt hhh] },
      have ttt: δ ≤ 0,
      { linarith [real.Inf_le I ⟨a, (λ y hy, (mem_Icc.1 hy.1).1)⟩ ⟨t, ge_iff_le.1 (le_of_lt r)⟩] },
      have m : 0 < 0,
      { linarith },
      exact nat.lt_asymm m m },
    { linarith[himI] } },
  exact ⟨Inf {x ∈ (Icc a b)| f x >= 0}, hI, hf⟩,
end

theorem bolzano (a b : ℝ) (hab : a < b) (f: ℝ → ℝ) (hf : continuous_on f (Icc a b)) (ha : (f a)*(f b)<0) : ∃ c ∈ (Icc a b), f(c)=0 :=
begin
  cases (mul_neg_iff.1 ha),
  {
    
    sorry
  },
  { exact bolz a b hab f hf h }
end