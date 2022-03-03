import basic_defs_world.level1 -- hide

/- Axiom : A topological space is a T₀ space if, from any two points in the topology, there exist and open set that contains one point and not the other
t0 : ∀ (x y : X) (h : y ≠ x) , ∃ (U : set X) (hU : is_open U), ((x ∈ U) ∧ (y ∉ U)) ∨ ((x ∉ U) ∧ (y ∈ U))
-/

/- Axiom : A topological space is a T₁ space if, from any two points in the topology, there exist and open set that contains the first point and not the second
t1 : ∀ (x y : X) (h : y ≠ x), ∃ (U : set X) (hU : is_open U), (x ∈ U) ∧ (y ∉ U)
-/

/-

# Level 1: Every Frechet space is a T₀ space

-/
variables {X : Type} -- hide
variables [topological_space X] -- hide

namespace topological_space -- hide

/- Lemma
Let τ be a topological space. If τ is a frechet space is also a T₀.
-/
lemma T1_is_T0: T1_space X → T0_space X :=
begin
  introI t1,
  fconstructor,
  intros x y hxy,
  obtain ⟨U, hU, hh⟩:= T1_space.t1 x y hxy,
  exact ⟨U, hU, or.inl hh⟩,









end

end topological_space -- hide
