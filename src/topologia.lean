import tactic
import data.set.finite
import for_mathlib

/-
# Building topological spaces in Lean
-/

/-
First a little setup, we will be making definitions involving the real numbers,
the theory of which is not computable, and we'll use sets.
-/
noncomputable theory
open set

/-
Definition of a topological space
-/
@[ext]
class topological_space (X : Type) :=
  (is_open : set X → Prop)
  (univ_mem : is_open univ)
  (union : ∀ (Y : set (set X)) (h : ∀ B ∈ Y, is_open B), is_open (⋃₀ Y))
  (inter : ∀ (A B : set X) (hA : is_open A) (hB : is_open B), is_open (A ∩ B))

namespace topological_space

/-- The empty set is open -/
@[simp]
lemma empty_mem {X : Type} [topological_space X] : is_open (∅ : set X) :=
begin
  rw ←sUnion_empty,
  apply union,
  tauto,
end

@[simp]
lemma univ_mem' {X : Type} [topological_space X] : is_open (univ : set X) := univ_mem

/-- The union of two open sets is open -/
lemma open_of_open_union_open {X : Type} [topological_space X] {U V : set X}
(hU : is_open U) (hV : is_open V): is_open (U ∪ V) :=
begin
  let I : set (set X) := {U, V},
  have H : ⋃₀ I = U ∪ V := sUnion_pair U V,
  rw ←H,
  apply union I,
  intros B hB,
  replace hB : B = U ∨ B = V, by tauto,
  cases hB; {rw hB, assumption},
end

/-- The intersection of a finite collection of open sets is open -/
lemma open_of_finite_set_opens {X : Type} [topological_space X] {S : set (set X)} (hfin : finite S)
(h : ∀ s ∈ S, is_open s) : is_open (sInter S) :=
begin
  revert h,
  apply finite.induction_on hfin,
  { simp },
  {
    intros U S hUS hSfin hind h,
    sorry
  }
end

/-- The open sets of the least topology containing a collection of basic sets -/
inductive generated_open (X : Type) (g : set (set X)) : set X → Prop
| univ : generated_open univ
| generating : ∀ A : set X,  A ∈ g → generated_open A
| sUnion : ∀ τ : set(set X), (∀ t, t ∈ τ → generated_open t) →
          generated_open ⋃₀ τ 
| inter : ∀ U V : set X,  generated_open U → generated_open V →
            generated_open (U ∩ V)

/-- The smallest topological space containing the collection `g` of basic sets -/
def generate_from {X : Type} (g : set (set X)) : topological_space X :=
{ is_open   := generated_open X g,
  univ_mem  := generated_open.univ,
  inter     := generated_open.inter,
  union     := generated_open.sUnion, }

def is_coarser {X : Type} (τ : topological_space X) (τ' : topological_space X) :=
  ∀ (U : set X), @is_open _ τ U → @is_open _ τ' U

/-- Given topologies τ and τ' on X, we say that τ ≤ τ' iff τ ⊆ τ' (as subsets) -/
instance top_has_le {X : Type} : has_le (topological_space X) :=
  ⟨λ τ τ', (∀ (U : set X), @is_open _ τ U → @is_open _ τ' U)⟩

/-- The topology generated from a collection of sets is the coarsest topology
  that contains those sets -/
lemma generated_open_is_coarsest {X : Type} (g : set (set X)) [τ : topological_space X]
(h : ∀ U ∈ g,  is_open U) : (generate_from g) ≤ τ :=
begin
  intros U hU,
  induction hU,
  { exact univ_mem },
  { apply h, assumption },
  { apply union; assumption },
  { apply inter; assumption },
end

end topological_space




namespace topological_space

noncomputable theory

def is_closed {X : Type} [topological_space X] := λ (C : set X), @is_open X _ (compl C)

def mk_closed_sets
  (X : Type)
  (σ : set (set X))
  (empty_mem : ∅ ∈ σ)
  (inter : ∀ B ⊆ σ, ⋂₀ B ∈ σ)
  (union : ∀ (A B ∈ σ), A ∪ B ∈ σ) :
topological_space X := {
  is_open :=  λ U, compl U ∈ σ,
  univ_mem := by simpa using empty_mem,
  union := 
  begin
    intros Y hY,
    rw compl_sUnion,
    apply inter (compl '' Y),
    simpa using hY,
  end,
  inter := 
  begin
    intros A B hA hB,
    rw compl_inter,
    exact union (compl A) (compl B) hA hB,
  end
  }

end topological_space

namespace topological_space
variables {X : Type}
variables [topological_space X] (x : X)  (A : set X)

def is_neighborhood := ∃ U, is_open U ∧ x ∈ U ∧ U ⊆ A

def is_interior_point := is_neighborhood x A

def interior := { x : X | is_interior_point x A }

lemma interior_def' : interior A = ⋃₀ {U : set X | is_open U ∧ U ⊆ A} :=
begin
  ext,
  split,
  {
    rintros ⟨U, is_open_U, x_in_U, U_subset_A⟩,
    use U,
    split,
    finish,
    exact x_in_U,
  },
  {
    rintros ⟨U, ⟨is_open_U, U_subset_A⟩, x_in_U⟩,
    use U,
    tauto,
  }
end

lemma interior_is_open : is_open (interior A) :=
begin
  rw interior_def',
  apply union,
  rintros B ⟨is_open_B, B_subset_A⟩,
  tauto,
end

lemma is_open_iff_eq_interior : is_open A ↔ A = interior A :=
begin
  split,
  {
    intro is_open_A,
    rw interior_def',
    ext1,
    split,
    {
      intro x_in_A,
      norm_num,
      use A,
      tauto,
    },
    {
      rintros ⟨hx,⟨⟨h₂, h₃⟩, h₄⟩⟩,
      tauto,
    }
  },
  { intro hA,
    rw hA, 
    exact interior_is_open A,
  }
end

-- més deures: definir adherència i propietats (pg 27)


end topological_space

