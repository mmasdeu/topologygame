import topologia
import .separacio

open topological_space
open set

variables (X : Type) [topological_space X]

/-- A topological space is (quasi)compact if every open covering admits a finite subcovering -/
def is_compact :=
  ∀ 𝒰 : set (set X), (∀ U ∈ 𝒰, is_open U) → 
  (⋃₀ 𝒰 = univ) → (∃ ℱ ⊆ 𝒰, finite ℱ ∧ ⋃₀ℱ = univ)

def is_compact_subset {X : Type} [topological_space X] (S : set X):=
  ∀ 𝒰 : set (set X), (∀ U ∈ 𝒰, is_open U) →
  (⋃₀ 𝒰 = S) → (∃ ℱ ⊆ 𝒰, finite ℱ ∧ ⋃₀ℱ = S)

lemma finite_set_is_compact (h : fintype X) : is_compact X :=
begin
  intros I hI huniv,
  exact ⟨I, rfl.subset, finite.of_fintype I, huniv⟩,
end

lemma for_compact_exist_open_disjont {A : set X} [hausdorff_space X] (h : is_compact_subset A) : ∀ (y : X), y ∈ Aᶜ  → 
  (∃ (V : set X), is_open V ∧ V ∩ A = ∅ ∧ y ∈ V) :=
begin
  intros y hy,
  let I := {V : set X | is_open V ∧ V ∩ A = ∅ ∧ y ∈ V},
  have hA : ∃ (ℱ : set (set X)), ℱ ⊆ I ∧  finite ℱ,
  {
    unfold is_compact_subset at h,
    have hIy : ∀ (B : set X), B ∈ I → is_open B, finish,
    sorry
  },
  cases hA with ℱ hℱ,
  have hℱo : ∀ (B : set X), B ∈ ℱ → is_open B,
  {
    intros B hB,
    have hIy : ∀ (B : set X), B ∈ I → is_open B, finish,
    exact hIy B (hℱ.1 hB),
  },
  have hℱy : ∀ (B : set X), B ∈ ℱ → y ∈ B,
  {
    intros B hB,
    have hIy : ∀ (B : set X), B ∈ I → y ∈ B, finish,
    exact hIy B (hℱ.1 hB),
  },
    have hℱA : ⋂₀ ℱ ∩ A = ∅,
    {
    apply subset.antisymm,
    {
      intros x hx,
      have hh : x ∈ ⋂₀ I → x ∉ A,
      {
        intro hhx,
        
        sorry
      },
      have hIy : x ∈ ⋂₀ ℱ → x ∉ A,
      {
        intro hhx,
        --finish,
        sorry
      },
      --library_search!,
      sorry
      --exact false.rec (x ∈ ∅) (hIy hx.1 hx.2),
    },
    exact (⋂₀ ℱ ∩ A).empty_subset,
  },
  exact ⟨⋂₀ ℱ, open_of_finite_set_opens hℱ.2 hℱo, hℱA, mem_sInter.mpr hℱy⟩, 
end

lemma compact_in_T2_is_closed {A : set X} [hausdorff_space X] (h : is_compact_subset A) : is_closed A :=
begin
  have hAc : interior Aᶜ = Aᶜ,
  {
    apply subset.antisymm,
      exact interior_is_subset Aᶜ,
    {
      intros x hxA,
      cases (for_compact_exist_open_disjont X h) x hxA with V hV,
      have hVAc : V ⊆ Aᶜ,
      {
        intros y hy,
        have hynA : y ∉ A,
        {
          intro hyA,
          have hyVA : y ∈ V ∩ A, by exact ⟨hy, hyA⟩,
          have hIe : V ∩ A ≠ ∅, by finish,
          exact hIe hV.2.1,
        },
        exact mem_compl hynA,
      },
      exact ⟨V, hV.1, hV.2.2, hVAc⟩,
    },
  },
  rw [is_closed, ← hAc],
  exact (interior_is_open Aᶜ),
end

/- Exemples de compacitat: topologica cofinita (definir-la) i demostrar compacitat -/
/- Conjunt finit → compacte ✓-/
/- Imatge contínua de compacte és compacte -/
/- Compacte dins d'un Hausdorff és tancat -/
/- Definir topologia de subespai -/
