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
variables {X : Type} [topological_space X]
variables (A B : set X)
open set

def is_neighborhood (x : X) := ∃ U, is_open U ∧ x ∈ U ∧ U ⊆ A

def interior := { x : X | is_neighborhood A x }

@[simp] lemma interior_subset_self : interior A ⊆ A :=
begin
  rintros x ⟨_, _⟩,
  tauto,
end


lemma interior_def' : interior A = ⋃₀ {U : set X | is_open U ∧ U ⊆ A} :=
begin
  simp only [interior, is_neighborhood, sUnion],
  ext,
  norm_num,
  tauto,
end

/--The interior of a set is open.-/
@[simp] lemma interior_is_open : is_open (interior A) :=
begin
  rw interior_def',
  apply union,
  rintros B ⟨is_open_B, _⟩,
  exact is_open_B,
end

lemma interior_maximal (hB : is_open B) (h: B ⊆ A ):  B ⊆ interior A  :=
begin
  intros x x_in_B,
  rw interior_def',
  use B,
  exact ⟨⟨hB, h⟩, x_in_B⟩,
end

/-- The interior of a set is the biggest open it contains. -/
lemma interior_is_biggest_open (hB : is_open B) : B ⊆ interior A ↔ (B ⊆ A) :=
begin
  split,
  { have := interior_subset_self A,
    tauto },
  {
    apply interior_maximal,
    exact hB,
  }
end 

/-These three properties characterize the interior-/
lemma interior_def'': is_open B ∧ B ⊆ A ∧ (∀ U, U ⊆ A → is_open U → U ⊆ B) ↔ B = interior A :=   
begin
  split,
  {
    rintros ⟨is_open_B, ⟨B_subset_A, B_is_biggest_open⟩⟩,
    apply subset.antisymm,
    {
      simpa [interior_is_biggest_open A B is_open_B],
    },
    {
      intros x ha,
      exact B_is_biggest_open (interior A) (interior_subset_self A) (interior_is_open A) ha,
    },
  },
  {
    intro,
    subst B,
    exact ⟨interior_is_open A, ⟨interior_subset_self A, λ U hUA hU, interior_maximal A U hU hUA⟩⟩,
  },
end 

@[simp] lemma eq_interior_iff_is_open : A = interior A ↔ is_open A :=
begin
  rw ← interior_def'',
  tauto,
end

/-- A point x is an adherent point of A if every neighborhood of x intersects A.-/
def is_adherent_point (x : X) := ∀ N, is_neighborhood N x → N ∩ A ≠ ∅

/-- The closure of A is the set of all the adherent points of A -/
def closure:= {x | is_adherent_point A x}

@[simp] lemma closure_supset_self : A ⊆ closure A :=
begin
  intros x hx,
  have hhx : is_adherent_point A x,
  {
    intros B hBx hn,
    unfold is_neighborhood at hBx,
    rcases hBx with ⟨D, hD, h⟩,
    exact eq_empty_iff_forall_not_mem.mp hn x (mem_inter (h.2 h.1) hx),
  },
  exact hhx,
end

@[simp] lemma closure_eq_compl_of_interior_compl: closure A = (interior Aᶜ)ᶜ :=
begin
  ext1,
  unfold interior is_neighborhood closure is_adherent_point is_neighborhood,
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
    intros a a_in_V,
    exact inter_is_not_is_empty_intersection (hV a_in_V) hU,
  }
end


lemma closure_def' : closure A = ⋂₀ {C : set X | is_closed C ∧ A ⊆ C} :=
begin
  rw [closure_eq_compl_of_interior_compl, interior_def', compl_sUnion],
  rw compl_image_set_of,
  simp only [compl_subset_compl, is_closed],
end

@[simp]
lemma subset_closed_inclusion_closure [topological_space X] {A B : set X}  (hB : is_closed B) :
  closure A ⊆ B ↔ A ⊆ B :=
begin
  split,
  { 
    have := closure_supset_self A,
    tauto,
  },
  {
    intros h x hx,
    rw closure_def' at hx,
    exact hx B ⟨hB, h⟩
  }
end

lemma subset_closed_inclusion_closure' [topological_space X] {A B : set X}  (hB : is_closed B) :
  A ⊆ B → closure A ⊆ B  := (subset_closed_inclusion_closure hB).mpr

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
  unfold interior is_neighborhood,
  ext,
  simp only [mem_inter_eq, mem_set_of_eq, subset_inter_iff],
  split,
  {
    intro h,
    obtain ⟨U, h1⟩ :=h,
    repeat {use U, tauto},
  },
  {
    rintro ⟨ha, hb⟩,
    obtain ⟨U, ⟨h1,h2,h3⟩⟩ := ha,
    obtain ⟨V, ⟨g1,g2,g3⟩⟩ := hb,
    use U ∩ V,
    repeat {split},
    { exact inter U V h1 g1 },
    repeat {tauto},
    {
      apply subset.trans _ h3,
      apply inter_subset_left,
    },
    {
      apply subset.trans _ g3,
      apply inter_subset_right,
    }
  },
end


def is_open_map {X Y : Type} [topological_space X] [topological_space Y]
(f : X → Y) :=  ∀ (V : set X), is_open V → is_open (f '' V)

def is_closed_map {X Y : Type} [topological_space X] [topological_space Y]
(f : X → Y) :=  ∀ (V : set Y), is_closed V → is_closed (f⁻¹' V)

/-- A function f : X → Y is continuous iff the preimage of every open set is open -/
def is_continuous {X Y : Type} [topological_space X] [topological_space Y]
(f : X → Y) :=  ∀ (V : set Y), is_open V → is_open (f⁻¹' V)

/-- The identity map is continuous. -/
lemma id_is_cont {X: Type} [topological_space X]: is_continuous (λ x : X, x) :=
begin
  tauto,
end

/-- The identity map is open. -/
lemma id_is_open {X: Type} [topological_space X]: is_open_map (λ x : X, x) :=
begin
  intros V hV,
  finish,
end

/-- The identity map is closed. -/
lemma id_is_closed {X: Type} [topological_space X]: is_closed_map (λ x : X, x) :=
begin
  tauto,
end

/-- The constant map is continuous. -/
lemma const_is_cont {X Y: Type} [topological_space X] [topological_space Y] (y: Y)
: is_continuous (λ x : X, y) :=
begin
  intros V hV,
  by_cases y ∈ V,
  {
    convert univ_mem,
    ext,
    tauto,
  },
  {
    convert empty_mem,
    ext,
    tauto,
  },
end

/-- The composition of continuous maps is continuous. -/
lemma comp_cont {X Y Z: Type} [topological_space X] [topological_space Y] [topological_space Z]
(f: X → Y) (hf: is_continuous f) (g: Y → Z) (hg: is_continuous g): is_continuous (g ∘ f) :=
begin
  intros U hU,
  specialize hg U hU,
  exact hf _ hg,
end

/-- The composition of open maps is open. -/
lemma comp_open {X Y Z: Type} [topological_space X] [topological_space Y] [topological_space Z]
(f: X → Y) (hf: is_open_map f) (g: Y → Z) (hg: is_open_map g): is_open_map (g ∘ f) :=
begin
  intros U hU,
  specialize hf U hU,
  specialize hg _ hf,
  rw image_image at hg,
  exact hg,
end

structure homeomorph (X Y : Type) [topological_space X] [topological_space Y]
  extends X ≃ Y :=
(continuous_to_fun  : is_continuous to_fun)
(continuous_inv_fun : is_continuous inv_fun) -- is_open_map to_fun

notation X `≅` Y := homeomorph X Y

 -- definir subespai i espai quocient
def top_induced (X Y : Type) [topological_space Y] (f : X → Y) : topological_space X :=
{ is_open := λ A, ∃ V, is_open V ∧ f⁻¹' V = A,
  univ_mem := ⟨univ,⟨univ_mem,by tauto⟩⟩,
  union := 
  begin
    rintros A hA,
    use ⋃₀{V : set Y | is_open V ∧ f⁻¹' V ∈ A},
    split,
    {
      rw sUnion,
      apply union,
      intros B hB,
      finish,
    },
    {
      rw preimage_sUnion,
      ext,
      norm_num,
      split,
      { tauto },
      { rintros ⟨U, hU, hx⟩,
        specialize hA U hU,
        rcases hA with ⟨V, hV, hV₂⟩,
        use V,
        rw ←hV₂ at hx hU,
        tauto },
    },
  end,
  inter := 
  begin
    intros A B hA hB,
    cases hA with U hU,
    cases hB with V hV,
    have h : f ⁻¹' (U ∩ V) = A ∩ B,
    {
      rw [← hV.2, ← hU.2],
      refl,
    },
    exact ⟨U ∩ V, inter U V hU.1 hV.1, h⟩,
  end
}

/-- La topologia quocient donada per una aplicació f : X → Y -/
def top_quotient (X Y : Type) [topological_space X] (f : X → Y) : topological_space Y :=
{ is_open := λ V, is_open (f⁻¹' V),
  univ_mem := 
  begin
    norm_num,
  end,
  union := 
  begin
    intros A hA,
    rw preimage_sUnion,
    apply union,
    rintros U ⟨hU, _⟩,
    subst U,
    apply union,
    rintros B ⟨hB, _⟩,
    subst B,
    exact hA hU hB,
  end,
  inter :=
  begin
    intros A B hA hB,
    rw preimage_inter,
    apply inter;
    assumption,
  end,
}



example (A B : set X) : A ⊆ B → interior A ⊆ interior B :=
begin
  intro h,
  apply (interior_is_biggest_open B (interior A) (interior_is_open _)).2,
  have h':= interior_subset_self A,
  tauto
end


end topological_space



-- Lemes previs de Kuratowski clausura i interior preserva inclusió,...
-- Definició de la banda de Möbius, via quocient i via subespai.
--  - demostrar que són homeomorfes.
