import data.set.basic -- hide
import data.set.finite -- hide
open set -- hide

/- Axiom : finite.induction_on

If P is a property of sets, to prove that P(s) is true for all *finite* sets s
it is enough to prove it for the empty set (h₀) and to prove
(h₁) that if s is a finite set and a ∉ s then P(s) →  P({a} ∪ s).

finite.induction_on {P : set α → Prop} {s : set α} (h : finite s)
  (h₀ : P ∅) (h₁ : ∀ {a s}, a ∉ s → finite s → P s → P (insert a s)) : P s
-/

/- Axiom : mem_insert_iff

We have x ∈ {a} ∪ s if and only if x = a or x ∈ s.

mem_insert_iff {x a : α} {s : set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s
-/

/- Axiom : sInter_empty

The empty intersection is everything.

sInter_empty : ⋂₀ ∅ = univ
-/


/- Axiom : sInter_insert
If T is a set of sets, and s is a set, the set-wise intersection ⋂₀ (s ∪ T) equals s ∩ ⋂₀ T.

sInter_insert (s : set α) (T : set (set α)) : ⋂₀ (insert s T) = s ∩ ⋂₀ T

-/


/-
This is the final level, and be advised that it is *much* harder than the previous ones.

We will use the following lemma when we start proving facts about topological spaces.

It seems clear that we want to use induction, so try to apply the `finite.induction_on`
lemma.

For the base case you will need `sInter_empty`, while for inductive step the lemmas `sInter_insert`, `mem_insert_iff` may be useful. Check the sidebar for their meaning.
-/


variables {X Y : Type} -- hide

/- Lemma :
If P is a property of sets which is closed under pairwise intersection then it is also closed under
arbitrary finite intersections.
-/
lemma sInter_of_inter {S : set (set X)} {P : set X → Prop} (hfin : finite S) (huniv : P univ) (hinter : ∀ A B : set X, P A → P B → P (A ∩ B))
 : (∀ s ∈ S, P s) → P ( sInter S ) :=
begin
  apply finite.induction_on hfin,
  {
    intro h,
    rwa sInter_empty,
  },
  {
    intros U S hUS hSfin hind h,
    rw sInter_insert,
    apply hinter,
    {
      apply h,
      rw mem_insert_iff,
      left, refl,
    },
    {
      apply hind,
      intros s hs,
      apply h,
      rw mem_insert_iff,
      right,
      exact hs,
    }
  },





end

