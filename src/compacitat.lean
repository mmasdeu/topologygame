import topologia

open topological_space
open set

/-- A topological space is (quasi)compact if every open covering admits a finite subcovering -/
def is_compact {X : Type} [topological_space X] :=
  ∀ 𝒰 : set (set X), (∀ U ∈ 𝒰, is_open U) →
  (⋃₀ 𝒰 = univ) → (∃ ℱ ⊆ 𝒰, finite ℱ ∧ ⋃₀ℱ = univ)

def is_compact_subset {X : Type} [topological_space X] (S : set X):=
  ∀ 𝒰 : set (set X), (∀ U ∈ 𝒰, is_open U) →
  (⋃₀ 𝒰 = S) → (∃ ℱ ⊆ 𝒰, finite ℱ ∧ ⋃₀ℱ = S)

/- Exemples de compacitat: topologica cofinita (definir-la) i demostrar compacitat -/
/- Conjunt finit → compacte -/
/- Imatge contínua de compacte és compacte -/
/- Compacte dins d'un Hausdorff és tancat -/
/- Definir topologia de subespai -/
