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
  (S ⊆ ⋃₀ 𝒰) → (∃ ℱ ⊆ 𝒰, finite ℱ ∧ S ⊆ ⋃₀ℱ )

lemma compact_space_iff_univ_compact :  is_compact X ↔ is_compact_subset (univ :set X) :=
begin
  split; intros h I hI hIX,
  { obtain ⟨F, hF, hh⟩ := h I hI (univ_subset_iff.mp hIX),
    exact ⟨F, hF, hh.1, hh.2.symm.subset⟩},
  { obtain ⟨F, hF, hh⟩ := h I hI (eq.symm hIX).subset,
    exact ⟨F, hF, hh.1, univ_subset_iff.mp hh.2⟩},
end

lemma finite_set_is_compact (h : fintype X) : is_compact X :=
begin
  intros I hI huniv,
  exact ⟨I, rfl.subset, finite.of_fintype I, huniv⟩,
end

lemma union_of_compacts_is_compact {A B : set X} (hA : is_compact_subset A) (hB : is_compact_subset B) : is_compact_subset (A ∪ B) :=
begin
  intros I hI huI,
  have hinclAB := union_subset_iff.1 huI,
  obtain ⟨FA, hFA, hhFA⟩ := hA I hI hinclAB.1,
  obtain ⟨FB, hFB, hhFB⟩ := hB I hI hinclAB.2,
  have hunion : A ∪ B ⊆ ⋃₀(FA ∪ FB),
  { rw  (sUnion_union FA FB),
    exact union_subset_union hhFA.right hhFB.right},
  exact ⟨FA ∪ FB, union_subset hFA hFB, hhFA.left.union hhFB.left, hunion⟩,
end

lemma empty_is_compact : is_compact_subset (∅ : set X) :=
begin
  intros I hI hhI,
  use ∅,
  exact ⟨ empty_subset I, finite_empty, by tauto⟩,
end

lemma finite_union_of_compacts_is_compact {I : set(set X)} (h : ∀ s ∈ I, is_compact_subset s) (hI : finite I) : is_compact_subset (⋃₀I):=
begin
  revert h,
  apply finite.induction_on hI,
  { intros I,
    rw sUnion_empty,
    apply empty_is_compact},
  { intros V T hVT hT hUT hs,
    have t : (⋃₀insert V T) = ⋃₀ T ∪ V, by finish,
    have hsT: (∀ (s : set X), s ∈ T → is_compact_subset s),
    { intros s hhs,
      exact hs s (mem_insert_of_mem V hhs)},
    rw t,
    exact union_of_compacts_is_compact X (hUT hsT) (hs V (mem_insert V T))},
end

lemma singleton_is_compact (x : X) : is_compact_subset ({x} : set X) :=
begin
  intros I hI hIincl,
  cases (bex_def.mp (hIincl  rfl)) with U hU,
  have hsingUI : {x} ⊆ ⋃₀{U},
  { rw (sUnion_singleton U),
    exact singleton_subset_iff.mpr hU.right},
  exact ⟨{U}, singleton_subset_iff.mpr hU.1, finite_singleton U, hsingUI⟩,  
end

lemma finite_subset_is_compact (A : set X): finite A → is_compact_subset A :=
begin
  intro h,
  apply finite.induction_on h,
  apply empty_is_compact,
  intros a s has hsfin hscpt,
  apply union_of_compacts_is_compact,
  apply singleton_is_compact,
  assumption,
end

lemma closed_subset_of_compact_is_compact {A B : set X} (hA : is_closed A) (hB : is_compact_subset B) (hAB : A ⊆ B) : 
  is_compact_subset A :=
begin
  intros I hI hIA,
  have hF : ∀ (U : set X), U ∈ I ∪ {Aᶜ} → is_open U,
  { intros U hU,
    cases ((mem_union U I {Aᶜ}).mp hU) with h,
      {exact hI U h},
      {rwa (mem_singleton_iff.mp h)}},
  have hUnionB : B ⊆ ⋃₀(I ∪ {Aᶜ}),
  { rw [sUnion_union I {Aᶜ}, Aᶜ.sUnion_singleton, (union_diff_cancel hAB).symm],
    exact union_subset_union hIA (inter_subset_right B Aᶜ)},
  obtain ⟨F, hFA, hh⟩  := hB (I ∪ {Aᶜ}) hF hUnionB,
  have hFI : F \ {Aᶜ} ⊆ I,
  { intros x hx,
    cases ((mem_union x I {Aᶜ}).mp (hFA ((diff_subset F {Aᶜ})  hx))) with h,
      {exact h},
      {exfalso,
       exact (not_mem_of_mem_diff hx) h}},
  have hsubsetU : A ⊆ ⋃₀(F \ {Aᶜ}),
  { intros x hx,
    rcases (mem_sUnion.1 ((subset.trans hAB hh.right) hx)) with ⟨V, ⟨hV1, hV2⟩⟩,
    exact (@mem_sUnion X x (F \ {Aᶜ})).2 ⟨V, ⟨hV1, by finish⟩, hV2⟩},
  exact ⟨F\{Aᶜ}, hFI, hh.left.subset (diff_subset F {Aᶜ}), hsubsetU⟩,
end

/-
lemma finite_subset_is_compact_using_choice (A : set X) (h : finite A) : is_compact_subset A :=
begin
  intros I hI huniv,
  have H : ∀ a ∈ A, ∃ ia ∈ I, a ∈ ia, by assumption,
  let f : A → set X := λ ⟨x, hxA⟩, classical.some (H x hxA),
  have hf1 : ∀ (x : X) (hx : x ∈ A), x ∈ (f ⟨x, hx⟩),
  {
    intros x hx,
    have hh := classical.some_spec (H x hx),
    tauto,
  },
  have hf2 : ∀ (x : X) (hx : x ∈ A), (f ⟨x, hx⟩) ∈ I,
  {
    intros x hx,
    have hh := classical.some_spec (H x hx),
    tauto,
  },
  use f '' univ,
  simp,
  split,
  {
    intros i hi,
    simp at hi,
    obtain ⟨x, ⟨hx,h'⟩⟩ := hi,
    subst h',
    tauto,
  },
  split,
  {
    haveI : fintype {x : X // x ∈ A} := finite.fintype h,
    apply finite_range f,
  },
  {
    unfold Union,
    intros x hx,
    unfold supr,
    rw Sup_eq_supr,
    simp,
    use f ⟨x,hx⟩,
    use x,
    use hx,
    tauto,
  }
end
 -/
open hausdorff_space

lemma tmp_lemma {X : Type} {A : set X} (F : set A) (hF1 : F.finite) : 
{x : X | ∃ (h : x ∈ A), (⟨x, h⟩ : A) ∈ F}.finite :=
begin
  sorry
end

lemma is_compact_set' {A : set X} {I : Type*} (h : is_compact_subset A) (U : I → set X) (hU : ∀ i, is_open (U i))
(hcov : A ⊆ ⋃₀ (U '' univ)): ∃ (F : set I), F.finite ∧ (A ⊆ ⋃₀ (U '' F)) :=
begin
  sorry
end

-- X : Type, i A : set X
-- per cada a ∈ A, triem Ua, Va oberts amb a ∈ Ua, y ∈ Va, Ua ∩ Va = ∅.
-- A ⊆ ⋃ Ua. A compacte -> subrecobriment finit Ua1,..., Uan.
-- V = ⋂ Vai. obert perquè intersecció finita. Aquest V funciona.
-- U : {a : X // a ∈ A} → set X, a ↦ Ua
lemma for_compact_exist_open_disjont{A : set X} [hausdorff_space X] (h : is_compact_subset A) (y : X) (hyA : ¬ y ∈ A) : 
  ∃ (V : set X), is_open V ∧ V ∩ A = ∅ ∧ y ∈ V :=
begin
  have UV : ∀ a ∈ A, ∃ UVa : set X × set X,
    is_open UVa.fst ∧ is_open UVa.snd ∧ UVa.fst ∩ UVa.snd = ∅ ∧ a ∈ UVa.fst ∧ y ∈ UVa.snd,
  {
    intros a ha,
    have hya : y ≠ a,
    {
      finish,
    },
    obtain ⟨U, V, H⟩ := t2 a y hya,
    exact ⟨⟨U, V⟩, by tauto⟩,
  },
  let U : A → set X := λ a, (classical.some (UV a.1 a.2)).fst,
  have hU : ∀ (a : A), is_open (U ⟨a.1, a.2⟩)
   := λ a, (classical.some_spec (UV a.1 a.2)).1,
  let V : A → set X := λ a, (classical.some (UV a.1 a.2)).snd,
  have hV : ∀ (a : A), is_open (V ⟨a.1, a.2⟩)
   := λ a, (classical.some_spec (UV a.1 a.2)).2.1,
  have hUV : ∀ (a : A), (U ⟨a.1, a.2⟩ ∩ V ⟨a.1, a.2⟩ = ∅)
   := λ a, (classical.some_spec (UV a.1 a.2)).2.2.1,
  have hUVa : ∀ (a : A), (a.1 ∈ U ⟨a.1, a.2⟩)
   := λ a, (classical.some_spec (UV a.1 a.2)).2.2.2.1,
  have hUVy : ∀ (a : A), (y ∈ V ⟨a.1, a.2⟩)
   := λ a, (classical.some_spec (UV a.1 a.2)).2.2.2.2,
  have hAcov : A ⊆ ⋃₀ (U '' univ),
  {
    intros a ha,
    specialize hUVa ⟨a, ha⟩,
    simp,
    use a,
    use ha,
    simp [hUVa],
  },
  have hfin : ∃ (F : set X), F.finite ∧ (A ⊆ ⋃₀ (U '' {x : A | x.1 ∈ F})),
  {
    obtain ⟨F, ⟨hF1,hF2⟩⟩ := is_compact_set' _ h U hU hAcov,
    use {x : X | ∃ f ∈ F, (f : X) = x},
    simp,
    split,
    {
      apply tmp_lemma,
      exact hF1,
    },
    {
      intros a ha,
      simpa using hF2 ha,
    }
  },
  obtain ⟨F, ⟨hf, h'⟩⟩ := hfin,
  have : fintype {a // a ∈ F},
  {
    apply fintype.of_finset (finite.to_finset hf),
    finish,
  },
  haveI: fintype {a // a ∈ F} := this,
  use ⋂₀ (V '' {x : A | x.1 ∈ F}),
  repeat {split},
  {
    apply open_of_finite_set_opens,
    {
      apply finite.image,
      refine finite.preimage _ hf,
      dsimp,
      intros x2 hx2 aa haa htmp,
      exact subtype.eq htmp,
    },
    intros s hs,
    simp at hs,
    obtain ⟨x, ⟨hx1, ⟨hxA, rfl⟩⟩⟩ := hs,
    finish,
  },
  {
    ext,
    simp,
    intros hx,
    intro hxA,
    specialize h' hxA,
    simp at h',
    obtain ⟨z, ⟨hz1, ⟨hz2, hz3⟩⟩⟩ := h',
    specialize hx z hz2 hz1,
    specialize hUV ⟨z, hz2⟩,
    simp at hUV,
    suffices : (U ⟨z, hz2⟩ ∩ V ⟨z, hz2⟩).nonempty,
    {
      replace this := nonempty.ne_empty this,
      tauto,
    },
    use x,
    exact ⟨hz3, hx⟩,
  },
  {
    simp,
    exact λ x hx1 hx2, hUVy ⟨x, hx1⟩,
  }
end

lemma compact_in_T2_is_closed {A : set X} [hausdorff_space X] (h : is_compact_subset A) : is_closed A :=
begin
  have hAc : interior Aᶜ = Aᶜ,
  { apply subset.antisymm,
      {exact interior_subset_self Aᶜ},
    { intros x hxA,
      cases (for_compact_exist_open_disjont X h) x hxA with V hV,
      have hVAc : V ⊆ Aᶜ,
      { intros y hy,
        have hynA : y ∉ A,
        { intro hyA,
          have hyVA : y ∈ V ∩ A, by exact ⟨hy, hyA⟩,
          have hIe : V ∩ A ≠ ∅, by finish,
          exact hIe hV.2.1},
        exact mem_compl hynA},
      exact ⟨V, hV.1, hV.2.2, hVAc⟩}},
  rw [is_closed, ← hAc],
  exact (interior_is_open Aᶜ),
end

/- Exemples de compacitat: topologica cofinita (definir-la) i demostrar compacitat -/

