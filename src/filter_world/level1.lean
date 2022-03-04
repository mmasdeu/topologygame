import filter_world.definition --hide

open set --hide
namespace filters --hide


/-
# Level 1: The principal filter of a subset
-/

def principal' {X : Type} (s : set X) := {t | s ⊆ t}


/- Lemma
The collection of subsets defined before have a filter structure.
-/
lemma principal_is_filter {X : Type} (s : set X) : is_filter (principal' s):=
begin
  fconstructor,
  {
    exact subset_univ s
  },
  {
    intros A B hA hAB,
    exact subset.trans hA hAB
  },
  {
    intros A B hA hB,
    exact subset_inter hA hB
  }


end
    

localized "notation `P` := principal" in filters -- hide

end filters --hide
