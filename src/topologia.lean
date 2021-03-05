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
    have h : ⋂₀ insert U S = (⋂₀ S) ∩ U,
    {
      finish,
    },
    rw h, 
    apply topological_space.inter;
    finish
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

@[simp] def is_closed {X : Type} [topological_space X] := λ (C : set X), @is_open X _ (compl C)

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
variables [topological_space X] (x : X)  (A B : set X)

def is_neighborhood := ∃ U, is_open U ∧ x ∈ U ∧ U ⊆ A

def is_interior_point := is_neighborhood x A

def interior := { x : X | is_interior_point x A }

@[simp] lemma interior_is_subset: interior A ⊆ A :=
begin
  rintros x ⟨_, _⟩,
  tauto,
end

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

/--The interior of a set is always open.-/
@[simp] lemma interior_is_open : is_open (interior A) :=
begin
  rw interior_def',
  apply union,
  rintros B ⟨is_open_B, B_subset_A⟩,
  tauto,
end

lemma interior_is_biggest_open: ∀ B, (B ⊆ A) → is_open B → B ⊆ interior A :=
begin
  intros B hB is_open_B x x_in_B,
  rw interior_def',
  use B,
  exact ⟨⟨is_open_B,hB⟩, x_in_B⟩,
end 

/-These three properties characterize the interior-/

lemma interior_def'': is_open B ∧ B ⊆ A ∧ (∀ U, U ⊆ A → is_open U → U ⊆ B) ↔ B = interior A :=   
begin
  split,
  {
    rintros ⟨is_open_B, ⟨B_subset_A, B_is_biggest_open⟩⟩,
    ext1,
    split,
    {
      apply interior_is_biggest_open A B B_subset_A is_open_B,
    },
    {
      intro ha,
      exact B_is_biggest_open (interior A) (interior_is_subset A) (interior_is_open A) ha,
    },
  },
  {
    intro,
    subst B,
    exact ⟨interior_is_open A, ⟨interior_is_subset A, interior_is_biggest_open A⟩⟩,
  },
end 

@[simp] lemma eq_interior_iff_is_open : A = interior A ↔ is_open A :=
begin
  split,
  {
    intro hA,
    rw hA, 
    exact interior_is_open A,
  },
  { 
    intro is_open_A,
    rw interior_def',
    ext1,
    split,
    {
      intro x_in_A,
      exact ⟨A, ⟨is_open_A, refl A⟩, x_in_A⟩,
    },
    {
      rintros ⟨U,⟨⟨_, U_subset_A⟩, x_in_U⟩⟩,
      --show_term{tauto,}, -- bug?
      exact U_subset_A x_in_U,
    },
  }
end

/-- A point x is an adherent point of A if every neighborhood of x intersects A.-/
def is_adherent_point := ∀ N, is_neighborhood x N → N ∩ A ≠ ∅

/-- The closure of A is the set of all the adherent points of A -/
def closure:= {x | is_adherent_point x A}

@[simp] lemma closure_eq_compl_of_interior_compl: closure A = (interior Aᶜ)ᶜ :=
begin
  ext1,
  unfold interior is_interior_point is_neighborhood closure is_adherent_point is_neighborhood,
  simp only [not_exists, and_imp, not_and, mem_set_of_eq, ne.def, exists_imp_distrib, mem_compl_eq],
  split,
  {
    intros hx U is_open_U x_in_U hU,
    let hhh := hx Aᶜ U is_open_U x_in_U hU,
    finish,
  },
  {
    intros hx U V is_open_V x_in_V hV hU,
    apply hx V is_open_V x_in_V,
    intros a a_in_V a_in_A,
    --is this in mathlib?
    have h: a ∈ U ∩ A,
    {
      split;
      tauto,
    },
    finish,
  }
end


lemma closure_def' : closure A = ⋂₀ {C : set X | is_closed C ∧ A ⊆ C} :=
begin
  have hh: (compl '' { U: set X | is_open U ∧ U ⊆ Aᶜ}) = {C: set X | is_closed C ∧ A ⊆ C},
  {
    ext1 V,
    split,
    {
      rintros ⟨U,⟨_, _⟩, Uh_right⟩,
      rw [is_closed, ← Uh_right],
      split,
      simp only [compl_compl],
      assumption,
      tauto,
    },
    {
      rintros ⟨_, _⟩,
      use Vᶜ,
      norm_num,
      tauto,
    },
  },
  rw [closure_eq_compl_of_interior_compl, interior_def', compl_sUnion, hh],
end

-- Not sure if this should be simp lemma. It is now solvable by simp.
@[simp] lemma closure_is_closed: is_closed (closure A) :=
begin
  simp only [interior_is_open, compl_compl, closure_eq_compl_of_interior_compl, is_closed],
end

@[simp] lemma eq_closure_iff_is_closed: A = closure A ↔ is_closed A:=
begin
  rw ←compl_inj_iff,
  simp only [compl_compl, eq_interior_iff_is_open, closure_eq_compl_of_interior_compl, is_closed],
end

-- Can we simplify this proof?
@[simp] lemma interior_interior: interior (interior A) = interior A :=
begin
  exact ((eq_interior_iff_is_open (interior A)).mpr (interior_is_open A)).symm,
end

@[simp] lemma closure_closure: closure (closure A) = closure A :=
begin
  simp only [compl_compl, closure_eq_compl_of_interior_compl, interior_interior],
end

lemma interior_inter: interior (A ∩ B) = interior A ∩ interior B :=
begin
  sorry,
end

/-- Kuratowski's problem -/
example: closure (interior (closure( interior A))) = closure (interior A) :=
begin
  sorry,
end

/-- Kuratowski's problem -/
example: interior (closure( interior (closure A))) = interior (closure A) :=
begin
  sorry,
end

def is_dense (A: set X) := closure A = univ

def boundary (A: set X) := closure A ∩ closure Aᶜ



-- Definir frontera
-- Definir (quasi)compacte
-- Axiomes de separació (T0, T1, T2, T3, Hausdorff )
-- Definir funció contínua
-- Afegir [simp] als lemes d'interior, clausura...
-- Afegir problemes al Game a partir dels exercicis de la secció 2.
end topological_space

