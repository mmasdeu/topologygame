import filter_world.level4 --hide
open set --hide
namespace filters --hide
localized "notation `P` := principal" in filters --hide

/-
# Level 5: The meet filter of two filters, greates lower bound
-/


/- Lemma
The meet of two filters is their greatest lower bound. 
-/
lemma meet_greatest_lower_bound {X : Type} (V F : filter X): ∀ (T : filter X), 
    T ≤ V ∧ T ≤ F → T ≤ meet V F :=
begin
  intros T hVF A hA,
  obtain ⟨v, f, hv, hf, H⟩ := hA,
  have hfv : v ∩ f ∈ T,
  {
    exact T.inter_sets (hVF.1 hv) (hVF.2 hf)
  },
  exact T.sets_of_superset hfv H,








end

end filters --hide