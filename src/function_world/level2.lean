import data.set.basic -- hide
import tactic -- hide
open set -- hide

open set function -- hide

variables {X Y I: Type} -- hide
/-
This level is similar to the previous one. You can use a similar strategy. 
The tactic *obtain* can be useful. 
-/

/- Lemma
If f is a function and A_i are sets, then f(⋃ A_i)=⋃ f(A_i)
-/
lemma image_Union (f: X → Y) ( A : I → set X) : f '' ( ⋃ i, A i ) = ⋃ i, f '' A i :=
begin 
  ext y,
  split,
  {
    intro h1,
    cases h1 with x hx, -- millor donar noms, per facilitar l'argument
    cases hx with hx1 hx2, -- no tenia bons noms, però almenys són més curts
    simp,
    rw ← hx2, --aquí voldria combinar dues hipotesis per obtenir el goal
    cases hx1 with U hU,
    simp at hU,
    cases hU with hU1 hU2,
    obtain ⟨i, hi⟩ := hU1,
    -- Ara hem de fer servir les hipòtesis que tenim...
    use i, -- l'index que busquem l'acabem d'obtenir al pas anterior
    use x,
    rw hi,
    exact ⟨hU2, rfl⟩,
  },
  {
    intro h1,
    simp at h1,
    cases h1 with i hx,
    simp,
    obtain  ⟨x, hx2⟩ := hx,
    cases hx2 with hxA hxy,
    use x,
    use i, 
  {
    exact hxA,
  },
  {
    exact hxy,
  },
  },
end
