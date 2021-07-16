import interior_world.level2 --hide

/-

# Level 3: The interior is open



-/
variables {X : Type} -- hide
variables [topological_space X] (x : X)  (A : set X) -- hide

namespace topological_space -- hide

/- Lemma
The interior of a set is open.
-/
@[simp] lemma interior_is_open : is_open (interior A) :=
begin
  rw interior_def',
  apply union,
  rintros B ⟨is_open_B, _⟩,
  exact is_open_B,











end


end topological_space -- hide
