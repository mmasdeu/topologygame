import data.set.basic -- hide
import tactic -- hide

/-
# Level 1: The image of a union

In this level we prove that the image of a union of two sets if the union of their images.
-/

open set -- hide
variables{X Y: Type} -- hide

/- Lemma
$ f(A ∪ B) = f(A) ∪ f(B) $
-/
lemma image_union (f : X → Y) (A B : set X) : f '' (A ∪ B) = f '' A ∪ f '' B :=
begin
  ext y,
  split,
  {
    intro h1,
    cases h1,
    cases h1_h,
    cases h1_h_left,
    {
      left, 
      rw <-h1_h_right,
      use [h1_w, h1_h_left],
    },
    {right,
    rw <-h1_h_right,
    use [h1_w, h1_h_left],
    },

  },
  {
    intro h1,
    cases h1,
    {
      cases h1,
      cases h1_h,
      rw <-h1_h_right,
      have h : h1_w ∈ A ∪ B,
      {
        left,
        exact h1_h_left,
      },
      use [h1_w, h],
    },
    {
      cases h1,
      cases h1_h,
      rw <-h1_h_right,
      have h : h1_w ∈ A ∪ B,
      {
        right,
        exact h1_h_left,
      },
      use [h1_w, h],
    },
  },

end