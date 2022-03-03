import tactic

class topological_space (X : Type) :=
  (is_open : set X → Prop)
  (univ_mem : is_open set.univ)
  (union : ∀ {Y : set (set X)} (h : ∀ U ∈ Y, is_open U), is_open (⋃₀ Y))
  (inter : ∀ {U V : set X} (hU : is_open U) (hV : is_open V), is_open (U ∩ V))

namespace topological_space

def is_neighborhood {X : Type} [topological_space X] (x : X) (A : set X) := ∃ U, is_open U ∧ x ∈ U ∧ U ⊆ A

def is_interior_point {X : Type} [topological_space X] (x : X) (A : set X) := is_neighborhood x A --hide

def interior  {X : Type} [topological_space X] (A : set X) := { x : X | is_neighborhood x A }

def is_closed {X : Type} [topological_space X] := λ (C : set X), @is_open X _ (compl C)

class T0_space (X : Type) [topological_space X]: Prop :=
(t0 : ∀ (x y : X) (h : y ≠ x) , ∃ (U : set X) (hU : is_open U), ((x ∈ U) ∧ (y ∉ U)) ∨ ((x ∉ U) ∧ (y ∈ U)))

class T1_space (X : Type) [topological_space X]: Prop := 
(t1 : ∀ (x y : X) (h : y ≠ x), ∃ (U : set X) (hU : is_open U), (x ∈ U) ∧ (y ∉ U)) 

class T1_space' (X : Type) [topological_space X]: Prop := 
(t1 : ∀ (x y : X) (h : y ≠ x), ∃ (U V: set X) (hU : is_open U) (hV : is_open V), (x ∈ U) ∧ (y ∉ U) ∧ (x ∉ V) ∧ (y ∈ V)) 

class T2_space (X : Type) [topological_space X]: Prop :=
(t2 : ∀ (x y : X) (h : y ≠ x), ∃ (U V: set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), (x ∈ U) ∧ (y ∈ V))

class T3_space (X : Type) [topological_space X] extends T0_space X: Prop :=
(regular : ∀ (x : X) (F : set X) (hF : is_closed F) (hxF: x ∉ F),
  ∃ (U V : set X) (hU : is_open U) (hV : is_open V) (hUV : U ∩ V = ∅), (x ∈ U) ∧ (F ⊆ V))

def continuous {X Y : Type} [topological_space X] [topological_space Y]
  (f: X → Y) : Prop
  := ∀ V : set Y, is_open V → is_open (f⁻¹'V)

end topological_space
