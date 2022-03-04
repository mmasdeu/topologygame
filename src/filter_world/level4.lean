import filter_world.level3 --hide
open set --hide
namespace filters --hide
localized "notation `P` := principal" in filters --hide

/-
# Level 4: The meet of a pair of filters
-/

def meet_set' {X : Type*} (V F : filter X) := {t | ∃ (v ∈ V) (f ∈ F), v ∩ f ⊆ t}

/- Lemma
The collection of subsets defined before is a filter.
-/
lemma is_filter_meet {X : Type} (V F : filter X): is_filter (meet_set' V F) :=
begin
  fconstructor,
  {
    exact ⟨univ, V.univ_sets, univ, F.univ_sets, (univ ∩ univ).subset_univ⟩
  },
  {
    rintros A B ⟨v, hv, f, hf, H⟩ hAB,
    exact ⟨v, hv, f, hf, subset.trans H hAB⟩
  },
  {
    rintros A B ⟨v₁, hv₁, f₁, hf₁, H₁⟩ ⟨v₂, hv₂, f₂, hf₂, H₂⟩,
    have : v₁ ∩ v₂ ∩ (f₁ ∩ f₂) = v₁ ∩ f₁ ∩ (v₂ ∩ f₂),
      by rwa [← inter_assoc, inter_assoc v₁, inter_comm v₂, ← inter_assoc, ← inter_assoc],
    obtain hvf := inter_subset_inter H₁ H₂,
    exact ⟨v₁ ∩ v₂, V.inter_sets hv₁ hv₂, f₁ ∩ f₂, F.inter_sets hf₁ hf₂, by rwa this⟩,
  }








end


def meet {α : Type*} (V F : filter α) : filter α := --hide
{ sets := {t | ∃ (v f : set α), v ∈ V ∧ f ∈ F ∧ v ∩ f ⊆ t }, --hide
  univ_sets := ⟨univ, univ, V.univ_sets, F.univ_sets, (univ ∩ univ).subset_univ⟩, --hide
  sets_of_superset := (λ A B ⟨v, f, hv, hf, H⟩ hAB, ⟨v, f, hv, hf, subset.trans H hAB⟩), --hide
  inter_sets := --hide
  begin --hide
    rintros A B ⟨v₁, f₁, hv₁, hf₁, H₁⟩ ⟨v₂, f₂, hv₂, hf₂, H₂⟩, --hide
    have : v₁ ∩ v₂ ∩ (f₁ ∩ f₂) = v₁ ∩ f₁ ∩ (v₂ ∩ f₂), --hide
      by rwa [← inter_assoc, inter_assoc v₁, inter_comm v₂, ← inter_assoc, ← inter_assoc], --hide
    obtain hvf := inter_subset_inter H₁ H₂, --hide
    exact ⟨v₁ ∩ v₂, f₁ ∩ f₂, V.inter_sets hv₁ hv₂, F.inter_sets hf₁ hf₂, by rwa this⟩ --hide
  end } --hide

end filters --hide