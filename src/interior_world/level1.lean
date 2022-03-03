import basic_defs_world.level1 -- hide

/- Axiom : A set A is the neighborhood of a point x if there is an open U such that x ∈ U ⊆ A.
is_neighborhood : ∃ U, is_open U ∧ x ∈ U ∧ U ⊆ A
-/

/- Axiom : A point x is an interior point of A if A is a neighborhood of x.
is_interior_point : is_neighborhood x A
-/

/- Axiom : The interior of a set A is the set of all its interior points. 
interior := { x : X | is_interior_point x A }
-/

/-
In this world we will end up having three alternative definitions of the interior of a set. 
This will be very useful, because at any point we will be able to choose the one that better fits our needs.

First of all we need to figure out what properties does the interior of an arbitrary set have... So we start with an easy one:

# Level 1: The interior is contained in the original set

-/
variables {X : Type} -- hide
variables [topological_space X] (x : X)  (A : set X) -- hide

namespace topological_space -- hide

@[simp]  -- hide
/- Lemma
The interior of any set A is contained in the set A.
-/
lemma interior_is_subset: interior A ⊆ A :=
begin
  rintros x ⟨_, _⟩,
  tauto,









end

end topological_space -- hide
