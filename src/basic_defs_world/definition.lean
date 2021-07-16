import tactic

class topological_space (X : Type) :=
  (is_open : set X → Prop)
  (univ_mem : is_open set.univ)
  (union : ∀ (Y : set (set X)) (h : ∀ U ∈ Y, is_open U), is_open (⋃₀ Y))
  (inter : ∀ (U V : set X) (hU : is_open U) (hV : is_open V), is_open (U ∩ V))
