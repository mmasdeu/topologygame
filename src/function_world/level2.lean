import data.set.basic -- hide
import tactic -- hide
open set -- hide

open set function -- hide

variables {X Y I: Type} -- hide
/-
# Level 1: The image of an indexed union

This level is similar to the previous one. You can use a similar strategy.

-/

/- Lemma
If f is a function and Aᵢ are sets, then f(⋃ Aᵢ) = ⋃ f(Aᵢ)
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
    cases hU1 with i hi,
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
    cases hx with x hx2,
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
