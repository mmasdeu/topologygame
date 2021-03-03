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

/- From a metric space we get an induced topological space structure like so: -/

instance {X : Type} [metric_space_basic X] : topological_space X :=
generate_from { B | ∃ (x : X) r, B = {y | dist x y < r} }

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

def ball {X : Type} [metric_space_basic X] (x : X) (r : ℝ) := {y | dist x y < r}

lemma balls_form_basis {X : Type} [metric_space_basic X] :
  basis_condition { B | ∃ (x : X) r, B = ball x r} :=
begin
  unfold ball,
  sorry
end

class metric_space (X : Type) extends topological_space X, metric_space_basic X :=
  (compatible : ∀ U, is_open U ↔ generated_open X { B | ∃ (x : X) r, B = {y | dist x y < r}} U)

--class metric_space (X : Type) extends topological_space X, metric_space_basic X :=
--  (compatible : ∀ (U : set X), is_open U ↔ (∀ x ∈ U, ∃ r > 0, (ball x r) ⊆ U))

--class metric_space (X : Type) extends topological_space X, metric_space_basic X :=
--  (compatible : ∀ (U : set X), is_open U ↔
--  @is_open _ (generate_from_basis (balls_form_basis)) U)



namespace metric_space

open topological_space

/- This might seem a bit inconvenient to have to define a topological space each time
we want a metric space.

We would still like a way of making a `metric_space` just given a metric and some
properties it satisfies, i.e. a `metric_space_basic`, so we should setup a metric space
constructor from a `metric_space_basic` by setting the topology to be the induced one. -/

def of_basic {X : Type} (m : metric_space_basic X) : metric_space X :=
{ compatible := begin intros,
sorry,
 --refl,
 end,
  ..m,
  ..metric_space_basic.topological_space}
 
/-- Open balls are open -/
lemma open_of_ball {X : Type} [metric_space X] {x : X} {r : ℝ} :
  is_open {y | dist x y < r} :=
begin
  fconstructor,
  simp,
  use x, use r,
end

end metric_space
