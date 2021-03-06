import tactic
import data.set.finite
import data.real.basic -- for metrics
import .topologia
import .bases

open set
open topological_space

/- # Metric spaces -/
noncomputable theory

class metric_space_basic (X : Type) :=
  (dist : X → X → ℝ)
  (dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y)
  (dist_symm : ∀ x y, dist x y = dist y x)
  (triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)

namespace metric_space_basic

@[simp]
lemma dist_eq_zero_iff' {X : Type} (x y : X) [metric_space_basic X] :
  dist x y = 0 ↔ x = y := dist_eq_zero_iff x y

lemma dist_nonneg {X : Type} [metric_space_basic X] (x y : X) : 0 ≤ dist x y :=
begin
  have h1 : dist x x = 0,
    rw (dist_eq_zero_iff x x).2, refl,
  suffices : 0 ≤ dist x y + dist x y,
  { linarith },
  rw ← h1,
  nth_rewrite_rhs 1 dist_symm x y,
  exact triangle _ _ _,
end


@[simp]
lemma dist_self_zero {X : Type} [metric_space_basic X] {x : X} : dist x x = 0 := by simp

def ball {X : Type} [metric_space_basic X] (x : X) (r : ℝ) := {y | dist x y < r}

@[simp]
lemma ball_def {X : Type} [metric_space_basic X] (x : X) (r : ℝ) : ball x r = { y | dist x y < r} := rfl

@[simp]
lemma mem_center_ball_iff {X : Type} [metric_space_basic X] {x : X} {r : ℝ} :
  x ∈ ball x r ↔ 0 < r :=
begin
  split;
  { exact λ h, by simpa using h },
end


lemma balls_form_basis {X : Type} [metric_space_basic X] :
 basis_condition { B | ∃ (x : X) r, B = {y | dist x y < r} } :=
begin
  fconstructor,
  {
    intro x,
    simp,
    use {y | dist x y < 1},
    use x, use 1,
    simp [dist_eq_zero_iff],
    linarith,
  },
  {
    intros U V hU hV,
    obtain ⟨x, r, hU⟩ := hU,
    obtain ⟨y, s, hV⟩ := hV,
    subst hU, subst hV,
    intros z hz,
    -- here is the proof that if z in B x r ∩ B y s then one can find some ball B ⊆ B x r ∩ B y s
    simp at hz,
    use ball z (min (r - dist x z) (s - dist y z)),
    simp,
    split,
    {
      use z, use (min (r - dist x z) (s - dist y z)),
      simp,
    },
    {
      split,
      { assumption },
      split,
      {
        intros a ha1 ha2,
        calc dist x a ≤ dist x z + dist z a : triangle x z a
            ... < r : lt_sub_iff_add_lt'.mp ha1,
      },
      {
        intros a ha1 ha2,
        calc dist y a ≤ dist y z + dist z a : triangle y z a
          ... < s : lt_sub_iff_add_lt'.mp ha2,
      },
    }
  }
end

end metric_space_basic

open metric_space_basic

instance prod.metric_space_basic (X Y : Type) [metric_space_basic X] [metric_space_basic Y] :
metric_space_basic (X × Y) :=
{ dist := λ u v, max (dist u.fst v.fst) (dist u.snd v.snd),
  dist_eq_zero_iff :=
  begin
    intro xy1,
    intro xy2,
    split,
    {
      intro h,
      have h1: dist xy1.fst xy2.fst ≥ 0 := dist_nonneg _ _,
      have h2: dist xy1.snd xy2.snd ≥ 0 := dist_nonneg _ _,
      have h3: dist xy1.fst xy2.fst = 0, 
      begin
        have h5 : max (dist xy1.fst xy2.fst) (dist xy1.snd xy2.snd) ≤ 0 :=
          by linarith,
        have h4 := max_le_iff.mp h5,
        linarith,
      end,

      have h6: dist xy1.snd xy2.snd = 0, 
      begin
        have h5 : max (dist xy1.fst xy2.fst) (dist xy1.snd xy2.snd) ≤ 0 := by linarith,
        have h4 := max_le_iff.mp h5,
        linarith,
      end,
      ext;
      {
        rw [←dist_eq_zero_iff _ _],
        tauto,
      },
     },
    {
      intro h,
      subst h, 
      rw (dist_eq_zero_iff xy1.fst xy1.fst).mpr (refl _),
      rw (dist_eq_zero_iff xy1.snd xy1.snd).mpr (refl _),
      exact max_self 0,
    },
  end,
  dist_symm := 
  begin
    intros xy1 xy2,
    simp only [dist_symm],
  end,
  triangle :=
   begin
    intros x y z,
    let  xy_X := (dist x.fst y.fst),
    let  yz_X := (dist y.fst z.fst),
    let  xy_Y := (dist x.snd y.snd),
    let  yz_Y :=  (dist y.snd z.snd),

    -- We introduce a refinement.
    calc  max (dist x.fst z.fst) (dist x.snd z.snd) ≤ (max (xy_X + yz_X) ( xy_Y + yz_Y)): by { apply max_le_max; exact triangle _ _ _ }
        ... ≤ max (dist x.fst y.fst) (dist x.snd y.snd) + max (dist y.fst z.fst) (dist y.snd z.snd):
     begin
      refine max_le_iff.mpr _,
      split;
      {
        apply add_le_add;
        finish,
      }, 
    end,
   end,
}

@[simp]
lemma prod_balls_def (X Y : Type) [metric_space_basic X] [metric_space_basic Y] {x : X} {y : Y} {r : ℝ} :
  (ball x r).prod (ball y r) = ball (x,y) r :=
begin
  unfold ball,
  unfold dist,
  ext,
  simp,
end

@[simp]
lemma prod_balls_def' (X Y : Type) [metric_space_basic X] [metric_space_basic Y] {x : X} {y : Y} {r : ℝ} :
  {z | dist x z < r}.prod {z | dist y z < r} = {z | dist (x,y) z < r} :=
begin
  ext,
  unfold dist,
  simp,
end

class metric_space (X : Type) extends topological_space X, metric_space_basic X :=
  (compatible : ∀ (U : set X), is_open U ↔ (∀ x ∈ U, ∃ r, 0 < r ∧ {y | dist x y < r} ⊆ U))


namespace metric_space

def ball {X : Type} [metric_space X] (x : X) (r : ℝ) := {y | dist x y < r}

@[simp]
lemma ball_def {X : Type} [metric_space X] (x : X) (r : ℝ) : ball x r = { y | dist x y < r} := rfl

open topological_space
open metric_space_basic

/-
We would still like a way of making a `metric_space` just given a metric and some
properties it satisfies, i.e. a `metric_space_basic`, so we should setup a metric space
constructor from a `metric_space_basic` by setting the topology to be the induced one. -/

lemma ball_subset_ball {X : Type} [metric_space X] {x : X} {r s : ℝ} (h : r ≤ s) :
  ball x r ⊆ ball x s :=
begin
  simp,
  intros a ha,
  linarith,
end

@[simp]
lemma mem_center_ball_iff {X : Type} [metric_space X] {x : X} {r : ℝ} :
  x ∈ ball x r ↔ 0 < r :=
begin
  split;
  { exact λ h, by simpa using h },
end

@[simp]
lemma ball_nonempty_iff {X : Type} [metric_space X] {x : X} {r : ℝ} :
  ball x r ≠ ∅ ↔ 0 < r :=
begin
  simp,
  split,
  {
    intro h,
    obtain ⟨z, hz⟩ := h,
    have H := dist_nonneg x z,
    linarith,
  },
  {
    intro h,
    use x,
    rw dist_self_zero,
    exact h,
  }
end

def of_basic {X : Type} (m : metric_space_basic X) : metric_space X :=
{ compatible := begin 
  intros,
  rw generate_from_basis_open_iff',
  simp,
  split,
  all_goals {
    intro h,
    intros x hx,
  },
  {
    obtain ⟨B, ⟨a, r, har⟩, ⟨hB1, hB2⟩⟩ := h x hx,
    subst har,
    use (r - dist a x), -- (Marc: I think that this is correct)
    simp at hB1 hB2,
    split,
    { linarith [hB1] },
    {
      apply subset.trans _ hB2,
      simp,
      intros z hz,
      calc dist a z ≤ dist a x + dist x z : triangle a x z
      ... < r : lt_sub_iff_add_lt'.mp hz,
    }
  },
  {
    obtain ⟨r, hr, hU⟩ := h x hx,
    use {y | dist x y < r},
    use x, use r,
    simp,
    split;
    simp [hr, hU],
  }
 end,
  ..m,
  ..generate_from_basis balls_form_basis
}

lemma ball_around_interior_point {X : Type} [metric_space X] {r : ℝ}
  {x y : X} (h: y ∈ ball x r) : ∃ s, 0 < s ∧ ball y s ⊆ ball x r :=
begin
  have : 0 < r,
  {
    have hne : ball x r ≠ ∅,
    {
      unfold ball,
      simp,
      use y,
      simpa using h,
    },
    apply (@ball_nonempty_iff X _ x r).1 hne,
  },
  use r - dist x y,
  split,
  { simpa using h },
  {
    simp,
    intros a ha,
    replace ha : dist x y + dist y a < r,
    { linarith },
    calc dist x a ≤ dist x y + dist y a : triangle x y a
      ... < r : ha,
  }
end

@[simp]
lemma metric_space_is_open_compatible {X : Type} [metric_space X] {U : set X} :
@is_open X (generate_from_basis balls_form_basis) U ↔ is_open U :=
begin
  simp [compatible, generate_from_basis_open_iff'],
  split,
  {
    intros h x hx,
    specialize h x hx,
    obtain ⟨B, ⟨⟨z, h, hB⟩, ⟨hz1, hz2⟩⟩⟩ := h,
    subst hB,
    simp at hz1 hz2,
    obtain ⟨s, hs, hsr⟩ := ball_around_interior_point hz1,
    use s,
    split,
    { exact hs },
    rw ←ball_def at hz2 ⊢,
    exact subset.trans hsr hz2,
  },
  {
    intros h x hx,
    obtain ⟨r, hr1, hr2⟩ := h x hx,
    use {y : X | dist x y < r},
    use x, use r,
    simp,
    tauto,
  }
end

/-- Open balls are open -/
lemma open_of_ball {X : Type} [metric_space X] {x : X} {r : ℝ} :
  is_open (ball x r) :=
begin
  have H:= @generate_from_basis_open_iff' X _ balls_form_basis {y : X | dist x y < r},
  simp at H ⊢,
  rw H,
  intros y hy,
  use {y : X | dist x y < r},
  use x, use r,
  { tauto },
end


/- unregister the bad instance we defined earlier -/
--local attribute [-instance] metric_space_basic.topological_space

end metric_space
