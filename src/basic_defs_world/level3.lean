import basic_defs_world.level2 --hide
import set_theory_world.level11 --hide
open set --hide
namespace topological_space --hide


/-
# Level 3: Intersection of a finite set of open sets is open.
-/

/- Hint : Click here for a hint, in case you get stuck.
The `sInter_of_inter` lemma will be of great help here.
-/

/- Lemma
The intersection of a finite set of open sets is open.
-/
lemma is_open_sInter {X : Type} [topological_space X] {S : set (set X)}
(hfin : finite S) (h : ∀ s ∈ S, is_open s): is_open (sInter S) :=
begin
  exact sInter_of_inter hfin univ_mem (λ A B hA hB, inter hA hB) h,







  
end

end topological_space --hide
