import game.interior_world.definition -- hide
import game.interior_world.level2 --hide

/-

# Level 4: The interior is ...



-/
variables {X : Type} -- hide
variables [topological_space X] (x : X)  (A : set X) -- hide

namespace topological_space -- hide

/- Lemma
The interior of a set ...
-/
lemma interior_is_biggest_open: ∀ B, (B ⊆ A) → is_open B → B ⊆ interior A :=
begin
  intros B hB is_open_B x x_in_B,
  rw interior_def',
  use B,
  exact ⟨⟨is_open_B,hB⟩, x_in_B⟩,










end 

end topological_space -- hide