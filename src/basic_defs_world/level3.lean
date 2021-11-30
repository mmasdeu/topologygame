import basic_defs_world.level1 --hide
open set --hide
namespace topological_space --hide


/-
# Level 3: Intersection of a finite set of open sets is open.
-/

/- Lemma
The intersection of a finite set of open sets is open.
-/
lemma is_open_sInter {X : Type} [topological_space X] {S : set (set X)}
(hfin : finite S) (h : ∀ s ∈ S, is_open s): is_open (sInter S) :=
begin
  revert h,
  apply finite.induction_on hfin,
  {
    intro h0,
    have key := @sInter_empty X,
    rw key,
    exact univ_mem,
  },
  intros a s has hs h1 h2,
  have h3 : ⋂₀ insert a s = (⋂₀ s)∩ a, by finish,
  rw h3,
  apply inter,
  finish,
  finish,
end

end topological_space --hide