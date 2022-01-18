import data.set.basic
import tactic

open set
variables{X Y: Type}
variable f : X → Y
variables A B : set X

example : f '' (A ∪ B) = f '' A ∪ f '' B :=
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