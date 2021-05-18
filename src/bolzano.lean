import topology.metric_space.basic

open set

lemma Inf.closure (I : set ℝ) (h : ∃ a, ∀ b∈ I, a ≤ b) : Inf I ∈ closure I :=
begin
  intros F hF,
  by_contradiction,
  have hIF : Inf I ∈ Fᶜ, by exact mem_compl h,  
  obtain ⟨ε, hε, H⟩  := metric.is_open_iff.1 (is_open_compl_iff.2 hF.1) (Inf I) hIF,
  --have hI : Inf I < Inf I + ε/2, by linarith,
  have hInf : Inf I + ε/2 ≤ Inf I,
  {
    obtain := real.le_Inf,
    sorry
  },
  linarith,
end

lemma bolz (a b : ℝ) (hab : a < b) (f: ℝ → ℝ) (hf : continuous_on f (Icc a b)) (ha : (f a)<0 ∧ (f b)>0) : ∃ c ∈ (Icc a b),f(c)=0 :=
begin
  let I := {x ∈ Icc a b | f x ≥ 0},
  have h1 : ∃ (x : ℝ), x ∈ I, by exact ⟨b, right_mem_Icc.2 (le_of_lt hab), ge_iff_le.1 (le_of_lt ha.2)⟩,
  have hb : Inf I ≤ b, by exact real.Inf_le {x ∈ Icc a b | f x ≥ 0} ⟨a, (λ y hy, (mem_Icc.1 hy.1).1)⟩ ⟨right_mem_Icc.2 (le_of_lt hab), ge_iff_le.2 (le_of_lt ha.2)⟩,
  cases ha with ha1 ha2,
  have hIIci : I = f⁻¹'(Ici 0) ∩ (Icc a b), by exact subset.antisymm (λ x hx, ⟨hx.2, hx.1⟩) (λ x hx, ⟨hx.2, hx.1⟩),
  have hII : is_closed I,
  { obtain ⟨U, hU⟩ := continuous_on_iff_is_closed.1 hf (Ici 0) (is_closed_Ici) ,
    rw [hIIci, hU.2],
    exact is_closed_inter hU.1 (is_closed_Icc) },
  have himI : 0 ≤ f (Inf I),
  { obtain hx := Inf.closure I ⟨a, (λ y hy, (mem_Icc.1 hy.1).1)⟩,
    rw (is_closed.closure_eq hII) at hx,
    exact hx.2 },
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
  { let g := λ (α : ℝ ), -α, 
    obtain ⟨c, H, hc⟩  := bolz a b hab (g ∘ f) (continuous_on.neg hf) ⟨neg_lt_zero.mpr h.1, neg_pos.mpr h.2⟩,
    exact ⟨c, H, neg_eq_zero.1 hc⟩ },
  { exact bolz a b hab f hf h }
end