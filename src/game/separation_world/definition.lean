import game.interior_world.definition -- hide

namespace topological_space -- hide

variables {X : Type}
--variables [topological_space X]   

class T0_space (X : Type) [topological_space X]: Prop :=
(t0 : ∀ (x y : X) (h : y ≠ x) , ∃ (U : set X) (hU : is_open U), ((x ∈ U) ∧ (y ∉ U)) ∨ ((x ∉ U) ∧ (y ∈ U)))

class T1_space (X : Type) [topological_space X]: Prop := 
(t1 : ∀ (x y : X) (h : y ≠ x), ∃ (U : set X) (hU : is_open U), (x ∈ U) ∧ (y ∉ U)) -- Marc : look up what's the best way to do this

class T1_space' (X : Type) [topological_space X]: Prop := 
(t1 : ∀ (x y : X) (h : y ≠ x), ∃ (U V: set X) (hU : is_open U) (hV : is_open V), (x ∈ U) ∧ (y ∉ U) ∧ (x ∉ V) ∧ (y ∈ V)) -- Marc : look up what's the best way to do this

def is_closed {X : Type} [topological_space X] := λ (C : set X), @is_open X _ (compl C)

theorem subset.antisymm {a b : set X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
set.ext $ λ x, ⟨@h₁ _, @h₂ _⟩

end topological_space -- hide