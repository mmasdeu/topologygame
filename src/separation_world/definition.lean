import interior_world.definition -- hide

namespace topological_space -- hide

variables (X : Type) [topological_space X]
--variables [topological_space X]   

def is_closed {X : Type} [topological_space X] := λ (C : set X), @is_open X _ (compl C)

class T0_space (X : Type) [topological_space X]: Prop :=
(t0 : ∀ (x y : X) (h : y ≠ x) , ∃ (U : set X) (hU : is_open U), ((x ∈ U) ∧ (y ∉ U)) ∨ ((x ∉ U) ∧ (y ∈ U)))

class T1_space (X : Type) [topological_space X]: Prop := 
(t1 : ∀ (x y : X) (h : y ≠ x), ∃ (U : set X) (hU : is_open U), (x ∈ U) ∧ (y ∉ U)) 

class T1_space' (X : Type) [topological_space X]: Prop := 
(t1 : ∀ (x y : X) (h : y ≠ x), ∃ (U V: set X) (hU : is_open U) (hV : is_open V), (x ∈ U) ∧ (y ∉ U) ∧ (x ∉ V) ∧ (y ∈ V)) 

class T2_space (X : Type) [topological_space X]: Prop :=
(t2 : ∀ (x y : X) (h : y ≠ x), ∃ (U V: set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), (x ∈ U) ∧ (y ∈ V))

class T3_space extends T0_space X: Prop :=
(regular : ∀ (x : X) (F : set X) (hF : is_closed F) (hxF: x ∉ F),
  ∃ (U V : set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), (x ∈ U) ∧ (F ⊆ V))

theorem subset.antisymm {a b : set X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
set.ext $ λ x, ⟨@h₁ _, @h₂ _⟩

end topological_space -- hide
