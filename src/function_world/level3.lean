import data.set.basic -- hide
import tactic -- hide
open set -- hide

open set function -- hide

variables {X Y I: Type} -- hide

/- Axiom :
mem_preimage : (a ∈ f ⁻¹' s) ↔ (f a ∈ s)
-/

/- Axiom :
mem_Inter : x ∈ (⋂ i, s i) ↔ ∀ i, x ∈ s i
-/

/-

# Level 3: The preimage of an intersection

To complete this level you will need to use the `mem_preimage` and `mem_Inter`
theorems, which you can find in the side bar.

-/


/- Lemma : no-side-bar
If f is a function and A_i are sets, then f⁻¹(⋂ A_i)=⋂ f⁻¹(A_i)
-/
lemma preimage_intersection_is_intersection (f: X → Y) ( A: I → set Y) : f ⁻¹'(⋂ i, A i)=⋂ i, f ⁻¹'  A i :=
begin 
ext y,
split,
{
  intro h,
  rw mem_preimage at h,
  rw mem_Inter at h ⊢,
  intro i,
  rw mem_preimage,
  exact h i,



},
{
  intro h,
  rw mem_Inter at h,
  rw mem_preimage,
  rw mem_Inter,
  intro i,
  rw ← mem_preimage,
  exact h i,


  
},

end