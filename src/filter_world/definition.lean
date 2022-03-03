import control.traversable.instances

open set

structure filter (α : Type*) :=
(sets                   : set (set α))
(univ_sets              : set.univ ∈ sets)
(sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)

structure is_filter {α : Type*} (sets : set (set α)):=
(univ_sets              : set.univ ∈ sets)
(sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)

def principal {α : Type*} (s : set α) : filter α :=
{ sets             := {t | s ⊆ t},
  univ_sets        := subset_univ s,
  sets_of_superset := λ x y hx, subset.trans hx,
  inter_sets       := λ x y, subset_inter }



instance {α : Type*}: has_mem (set α) (filter α) := ⟨λ U F, U ∈ F.sets⟩

variables {α : Type} {f g : filter α} {s t : set α}

lemma filter_eq : ∀ {f g : filter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl



instance : partial_order (filter α) :=
{ le            := λ f g, ∀ ⦃U : set α⦄, U ∈ g → U ∈ f,
  le_antisymm   := λ a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := λ a, subset.rfl,
  le_trans      := λ a b c h₁ h₂, subset.trans h₂ h₁ }

theorem le_def {f g : filter α} : f ≤ g ↔ ∀ x ∈ g, x ∈ f := iff.rfl

