--import game.definition -- hide
import game.level1 --hide

namespace topological_space -- hide

variables {X : Type}
variables [topological_space X] (x : X)  (A B : set X)

def is_neighborhood := ∃ U, is_open U ∧ x ∈ U ∧ U ⊆ A

def is_interior_point := is_neighborhood x A

def interior := { x : X | is_interior_point x A }


end topological_space -- hide
