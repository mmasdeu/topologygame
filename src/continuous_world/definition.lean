import tactic

import basic_defs_world.definition

open topological_space

variables {X : Type} {Y: Type}
variables [topological_space X][topological_space Y]

def continuous(f: X → Y): Prop
  := ∀ V : set Y, is_open V → is_open (f⁻¹'V)

