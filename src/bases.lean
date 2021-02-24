import .topologia
open set
open topological_space

variables {X : Type}

def is_basis [topological_space X] (I : set (set X)) : Prop :=
(∀ {B : set X}, B ∈ I → is_open B) ∧ 
(∀ U, ∀ x, is_open U → x ∈ U → ∃ B ∈ I, x ∈ B ∧ B ⊆ U)

class basis_condition (I : set (set X)) :=
(univ : univ = ⋃₀I)
(filter : ∀ U V ∈ I, ∀ x ∈ U ∩ V, ∃ W ∈ I, x ∈ W ∧ W ⊆ U ∩ V)

lemma basis_condition_inter (ℬ : set (set X)) [basis_condition ℬ] {U V : set X}
(hU : U ∈ ℬ) (hV : V ∈ ℬ) : ∃ J ⊆ ℬ, U ∩ V = ⋃₀ J :=
begin
  use {W | W ∈ ℬ ∧ W ⊆ U ∩ V },
  split,
  {
    norm_num,
    intros x hx,
    simp at hx,
    exact hx.1,
  },
  {
    ext,
    split,
    {
      intro hx,
      norm_num,
      have hh := basis_condition.filter U V hU hV x hx,
      obtain ⟨W, hW1, hW2, hW3⟩ := hh,
      use W,
      finish,
    },
    {
      intro hx,
      simp at hx,
      obtain ⟨a, ⟨ha1, ha2, ha3⟩, hxa⟩ := hx,
      suffices : a ⊆ U ∩ V,
      {
        exact this hxa,
      },
      exact subset_inter ha2 ha3,
    }
  }
end

lemma basis_has_basis_condition [topological_space X] {I : set (set X)} (h: is_basis I):
  basis_condition I := {
    univ := 
    begin
      ext,
      simp,
      have hunivopen: is_open univ, by simp [univ_mem],
      have h2 := h.2 univ x hunivopen (mem_univ x),
      tauto,
    end
    ,
    filter := 
    begin
      intros U V hU hV x hx,
      have hUopen: is_open U := h.1 hU,
      have hVopen : is_open V := h.1 hV,
      have hUVopen : is_open (U ∩ V),
      {
        apply inter;
        assumption,
      },
      apply h.2;
      assumption,
    end
     }

/-- A basis defines a topological space, by decreeing open the arbitrary
  unions of basis elements --/
def generate_from_basis {ℬ : set (set X)} (h: basis_condition ℬ):
  topological_space X := {
  is_open := λ U, ∃ J ⊆ ℬ, U = ⋃₀ J,
  univ_mem := ⟨ℬ, ⟨rfl.subset, h.univ⟩⟩,
  union :=
  begin
    intros Y hY,
    simp at hY,
    choose ι h using hY,
    have h1 := λ y hy, (h y hy).1,
    have h2 := λ y hy, (h y hy).2,
    clear h,
    norm_num,
    use ⋃ (y : set X) (hy : y ∈ Y), ι y hy,
    rw ←sUnion_bUnion h2,
    simp,
    intros x hx,
    simp at hx,
    obtain ⟨y, hy1, hy2⟩ := hx,
    specialize h1 y hy1,
    tauto,
  end,
  inter := 
  begin
    intros U V hU hV,
    obtain ⟨J, hJ1, hJ2⟩ := hU,
    obtain ⟨K, hK1, hK2⟩ := hV,
    have hUV : U ∩ V = ⋃₀ J ∩ ⋃₀ K,
    {
      exact congr (congr_arg has_inter.inter hJ2) hK2,
    },
    rw sUnion_inter_sUnion at hUV,
    suffices : ∀ x ∈ U ∩ V, ∃ W ∈ ℬ, x ∈ W ∧ W ⊆ U ∩ V,
    {
      use {W ∈ ℬ | W ⊆ U ∩ V},
      split,
      {
        intro W,
        simp,
        tauto,
      },
      {
        ext,
        split,
        {
          intro hx,
          specialize this x hx,
          obtain ⟨W, hW⟩ := this,
          simp at hW,
          simp,
          use W,
          tauto,
        },
        {
          intro hx,
          simp at hx,
          obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := hx,
          have : a ⊆ U ∩ V,
          {
            norm_num,
            exact ha2,
          },
          tauto,
        }
      },
    },
    intros x hx,
    rw hUV at hx,
    simp at hx,
    obtain ⟨j, k, ⟨hjk1, hjk2⟩, hjk3, hjk4 ⟩ := hx,
    have hh : ∃ W ∈ ℬ, x ∈ W ∧ W ⊆ j ∩ k,
    {
      apply basis_condition.filter,
      tauto,
      tauto,
      finish,
    },
    obtain ⟨W, hxW, hWjk⟩ := hh,
    use W,
    have hWUV : W ⊆ U ∩ V,
    {
      have hjU : j ⊆ U,
      {
        rw hJ2,
        apply subset_sUnion_of_mem hjk1,
      },
      have hkV : k ⊆ V,
      {
        rw hK2,
        apply subset_sUnion_of_mem hjk2,
      },
      have hjkUV : j ∩ k ⊆ U ∩ V := inter_subset_inter hjU hkV,
      --replace hWjk := hWjk.2,
      tauto,
    },
    tauto,
  end
  }

lemma generate_from_basis_simp {X : Type} {I : set (set X)} (h: basis_condition I) : 
  generate_from I = generate_from_basis h :=
begin
  ext U,
  split,
  {
    intro hU,
    induction hU with V hV J hJ h W1 W2 hW1 hW2 hW1' hW2',
    {
      simp [univ_mem],
    },
    {
      fconstructor,
      use {V},
      finish,
    },
    {
      apply union,
      assumption,
    },
    {
      apply inter;
      assumption,
    }
  },
  {
    intro hU,
    induction hU with J hJ,
    simp at hJ,
    rw hJ.2,
    apply union,
    intros V hV,
    fconstructor,
    replace hJ := hJ.1,
    solve_by_elim,
  }
end

/-- A set ℬ satisfying the basis condition is a basis for the topology it generates -/
lemma prop22 (ℬ : set (set X)) (h : basis_condition ℬ) :
  @is_basis _ (generate_from_basis h) ℬ :=
begin
  unfold is_basis,
  split,
  {
    intros B hB,
    use {B},
    exact ⟨singleton_subset_iff.mpr hB, by simp⟩,
  },
  {
    intros U x hU hx,
    induction hU with J hJ,
    simp at hJ,
    have hxJ: ∃ Uj ∈ J, x ∈ Uj,
    {
      rw [hJ.2, mem_sUnion] at hx,
      assumption,
    },
    obtain ⟨Uj, hUjJ, hUjx⟩ := hxJ,
    use Uj,
    have hUjI : Uj ∈ ℬ,
    {
      replace hJ := hJ.1,
      tauto,
    },
    have Uj_in_U : Uj ⊆ U,
    {
      rw hJ.2,
      apply subset_sUnion_of_subset J Uj _ hUjJ,
      tauto,
    },
    exact ⟨hUjI,hUjx,Uj_in_U⟩,
  }
end
