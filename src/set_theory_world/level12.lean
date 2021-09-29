import data.set.basic -- hide
open set -- hide

variables {X Y : Type} -- hide

/- Lemma : no-side-bar
Giving two subsets of a type `A₁ ⊆ X` `A₂ ⊆ X` and two of another type `B₁ ⊆ Y` `B₂ ⊆ Y`
satisfying `A₁ ⊆ A₂` and `B₁ ⊆ B₂`, we can prove that `A₁ × B₁ ⊆ A₂ × B₂` (as products of sets).
-/
lemma sInter_of_inter {A₁ A₂ : set X} {B₁ B₂ : set Y} (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
  A₁.prod B₁ ⊆ A₂.prod B₂ :=
begin
  intros x hx,
  exact ⟨hA hx.1, hB hx.2⟩,
end