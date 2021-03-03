import .topologia
import .metrics
import data.set.finite
import data.real.basic -- for metrics

open set
open topological_space

noncomputable theory

/- Now it is quite easy to give a topology on the product of a pair of
   topological spaces. -/
instance prod.topological_space (X Y : Type) [topological_space X]
  [topological_space Y] : topological_space (X × Y) :=
topological_space.generate_from {U | ∃ (Ux : set X) (Uy : set Y)
  (hx : is_open Ux) (hy : is_open Uy), U = set.prod Ux Uy}

lemma is_open_prod (X Y : Type) [topological_space X] [topological_space Y]
 {U : set X} {V : set Y} (hU : is_open U) (hV : is_open V) : is_open (U.prod V) :=
begin
  fconstructor,
  simp,
  exact ⟨U, hU, ⟨V, ⟨hV,rfl⟩⟩⟩,
end

lemma is_open_prod_iff {X Y : Type} [topological_space X] [topological_space Y]
  {s : set (X × Y)} :
  is_open s ↔ (∀a b, (a, b) ∈ s → ∃u v, is_open u ∧ is_open v ∧
  a ∈ u ∧ b ∈ v ∧ set.prod u v ⊆ s) := 
  begin
    split,
    {
      intros h_s a b h_ab,
      induction h_s with w hw ℬ hh h₁ h₂ h₃ h₄ h₅ h₆ h₇,
      {
        let h := (univ: set X).prod (univ: set Y),
        exact ⟨univ, univ, univ_mem, univ_mem, trivial, trivial, h.subset_univ⟩,
      },
      {
        rcases hw with ⟨w_x, ⟨w_y, ⟨h_x, ⟨h_y, hh⟩⟩⟩⟩,
        use w_x, 
        use w_y,
        repeat {split},
        all_goals {try {finish} },
      },
      {
        rcases h_ab with ⟨U, hU_1, hU_2⟩,
        let h1 := h₁ U hU_1 hU_2,
        norm_num at h1,
        obtain ⟨u, h_u⟩ := h1,
        cases h_u with is_open_u h_uv,
        obtain ⟨v, h_v⟩ := h_uv,
        use u, use v,
        repeat {split},
        all_goals {try {tauto}},
        intros a ha,
        use U,
        tauto,
      },
      {
        cases h_ab,
        have h1 : ∃ (u : set X) (v : set Y), is_open u ∧ is_open v ∧ a ∈ u ∧ b ∈ v ∧ u.prod v ⊆ h₂,
        {
          apply h₆,
          tauto,
        },
        have h2 : ∃ (u : set X) (v : set Y), is_open u ∧ is_open v ∧ a ∈ u ∧ b ∈ v ∧ u.prod v ⊆ h₃,
        {
          apply h₇,
          tauto,
        },
        rcases h1 with ⟨x1, y1, is_open_x1, is_open_y1, a_in_x1, b_in_y1, prod_in_h2⟩,
        rcases h2 with ⟨x2, y2, is_open_x2, is_open_y2, a_in_x2, b_in_y2, prod_in_h3⟩,
        use x1 ∩ x2,
        use y1 ∩ y2,
        repeat {split},
        all_goals {
          try {apply topological_space.inter},
          try {tauto},
          try {assumption},
        },
        intros xy h_xy,
        have h1: (x1 ∩ x2).prod (y1 ∩ y2) ⊆ x1.prod y1,
          by simp [←prod_inter_prod],
        have h2: (x1 ∩ x2).prod (y1 ∩ y2) ⊆ x2.prod y2,
          by simp [←prod_inter_prod],
        split;
        tauto,
      }
    },
    {
      intro h,
     let Opens : set (set (X × Y)):=
       { uv | ∃ (u: set X) (v : set Y), uv = (set.prod u v) ∧ is_open u ∧ is_open v ∧ (set.prod u v) ⊆ s},
     have h_s : s = ⋃₀ Opens,
     begin
       ext1,
       split,
       {
         cases x with x y,
         intro h_xy,
         norm_num,
         have hh := h x y h_xy,
         obtain ⟨u, v, is_open_u, is_open_v, x_in_u, y_in_v, uv_in_s⟩ := hh,
         use set.prod u v,
         use u,
         use v,
         tauto,
         finish,
    },
       {
         intro h_Opens,
         obtain ⟨U, ⟨x, y, U_eq_xy, is_open_x, is_open_y, xy_subset_s⟩, x_in_U⟩ := h_Opens,
         apply xy_subset_s,
         finish,
       }
     end,
     rw h_s,
     apply topological_space.union,
     intros B hB,
     simp at *,
     obtain ⟨x, y, B_is_xy, is_open_x, is_open_y, h_xy⟩ := hB,
     fconstructor,
     norm_num,
     use x,
     split,
     exact is_open_x,
     use y,
     split; assumption,
    },
  end


lemma is_open_prod_balls {X Y : Type} (r : ℝ) [metric_space X] [metric_space Y]
  (xy : X × Y) : is_open {zt : X × Y | metric_space_basic.dist xy.1 zt.1 < r ∧
  metric_space_basic.dist xy.2 zt.2 < r} :=
begin
  change is_open ({x : X | metric_space_basic.dist xy.1 x < r}.prod 
  {y : Y | metric_space_basic.dist xy.2 y < r}),
  apply is_open_prod;
  apply metric_space.open_of_ball,
end


/- Now lets define the product of two metric spaces properly -/
instance {X Y : Type} [metric_space X] [metric_space Y] : metric_space (X × Y) :=
{ compatible :=
  begin
    intro U,
    split,
    {
      intro hU, 
      induction hU with V hVW g h₁ h₂ V W h1 h2 h3 h4,
      {
         -- library_search behaves oddly
         apply univ_mem,
      },
      {
        simp at *,
        obtain ⟨V,hV,W,⟨hW,hprod⟩⟩ := hVW,
        subst hprod,
        unfold ball,
        unfold metric_space_basic.dist,
        simp,
        sorry
      },
      {
        -- library_search behaves oddly
        apply union,
        intros B hB,
        tauto,
      },
      { 
        -- library_search behaves oddly
        apply inter;
        tauto,
      },
    },
    {
      intro h,
      induction h with V h,
      {
        cases h,
        subst U,
        apply union,
        intros B B_in_V,
        norm_num,
        have h: ∃ x r, B = ball x r,
        {
          tauto,
        },
        rcases h with ⟨xy, r, _⟩,
        subst B,
        sorry,
      },
    },
  end,
  ..prod.topological_space X Y,
  ..prod.metric_space_basic X Y
}