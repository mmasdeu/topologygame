import basic_defs_world.level1 -- hide
import tactic -- hide

/-
# Level 1: The identity function is continuous

In this level we prove that the identity function is continuous.

-/

/- Definition : A function between two topologies is continuous if the preimage of an open set is an open set.
-/

open set -- hide
open topological_space -- hide
variables {X Y: Type} [topological_space X] -- hide


/- Lemma
The idententiy function is continuous.
-/
lemma id_is_continuous (f : X → X) : continuous (λ x: X, x) :=
begin
  intros V hV,
  unfold preimage,
  rw set_of_mem_eq,
  exact hV,








end
