import basic_defs_world.definition -- hide

/- Axiom : The total set (called `univ`) is open.
univ_mem : is_open set.univ
-/

/- Axiom : The intersection of two open sets is open.
inter : ∀ (U V : set X) (hA : is_open U) (hB : is_open V), is_open (U ∩ V)
-/

/- Axiom : The union of an arbitrary set of open sets is open.
union : ∀ (Y : set (set X)) (h : ∀ U ∈ Y, is_open U), is_open (⋃₀ Y)
-/

/- Axiom : The union over the empty set is empty.
sUnion_empty : ⋃₀ ∅ = ∅
-/

/-
# Level 1 : The empty set is open.
-/
noncomputable theory -- hide
open set -- hide

/-
In many textbooks, one of the axioms of a topological space is that the empty set is open. This actually follows from the other axioms!
-/

namespace topological_space -- hide


/- Hint : Click here for a hint, in case you get stuck.
In Lean, sets are notation for logical statements. That is, the set
`a ∈ { x : X | P x }` means *the same as* `P a`. As a somewhat degenerate
example, `a ∈ ∅` means `false`.
-/

/- Lemma
Prove that the empty set is open.
-/
lemma is_open_empty {X : Type} [topological_space X] : is_open (∅ : set X) :=
begin
  rw ←sUnion_empty,
  apply union,
  tauto,





end

end topological_space -- hide
