import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

/-! A shared midpoint keeps both contact rows inside one inactive-coordinate fibre. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre

open Finset
open BalancedCriticalSpectrum (Q flip)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open private differingAxes differingAxes_foldl_flip mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

/-- The fibre of a midpoint obtained by freezing all coordinates outside `A`. -/
def sameFibre (A : Finset (Fin 9)) (z u : Q 9) : Prop :=
  ∀ k, k ∉ A → u k = z k

open Classical in
/-- Restrict a support to the fibre through `z` with active coordinates `A`. -/
noncomputable def restrictToFibre (S : Finset (Q 9)) (A : Finset (Fin 9)) (z : Q 9) : Finset (Q 9) :=
  S.filter (sameFibre A z)

private theorem diff_pair (u : Q 9) {i j : Fin 9} (hij : i ≠ j) :
    differingAxes u (flip (flip u i) j) = {i, j} := by
  simpa using differingAxes_foldl_flip [i, j] (by simp [hij]) u

private theorem cross_pair_axes_active
    {C D : Finset (Q 9)} {A : Finset (Fin 9)} {b : Bool} {z : Q 9}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hpar : ∀ x ∈ C, parity x = b)
    (hmask : ∀ T ∈ minimumDisplacements C D b 2, T ⊆ A)
    {i j : Fin 9} (hi : flip z i ∈ C) (hj : flip z j ∈ D) :
    i ∈ A ∧ j ∈ A := by
  have hij : i ≠ j := by
    intro he
    subst j
    have h := hsep _ hi _ hj
    simp at h
  have hpair : ({i, j} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
    have he : differingAxes (flip z i) (flip z j) = {i, j} := by
      simpa only [BalancedCriticalSpectrum.flip_flip] using diff_pair (flip z i) hij
    have hd : hammingDist (flip z i) (flip z j) = 2 := by
      change (differingAxes (flip z i) (flip z j)).card = 2
      rw [he, Finset.card_pair hij]
    exact mem_minimumDisplacements.mpr ⟨_, hi, _, hj, hpar _ hi, hd, he⟩
  have hsub := hmask _ hpair
  exact ⟨hsub (by simp), hsub (by simp)⟩

private theorem flip_same_fibre {A : Finset (Fin 9)} {z : Q 9} {i : Fin 9}
    (hi : i ∈ A) : sameFibre A z (flip z i) := by
  intro k hk
  have hki : k ≠ i := by
    intro h
    exact hk (h ▸ hi)
  simp [sameFibre, BalancedCriticalSpectrum.flip, hki]

private theorem directions_restrictToFibre_eq
    {S : Finset (Q 9)} {A : Finset (Fin 9)} {z : Q 9}
    (hactive : directions S z ⊆ A) :
    directions S z = directions (restrictToFibre S A z) z := by
  classical
  ext i
  constructor
  · intro hi
    apply (mem_directions _ _ _).mpr
    refine mem_filter.mpr ⟨(mem_directions S z i).mp hi, ?_⟩
    exact flip_same_fibre (hactive hi)
  · intro hi
    exact (mem_directions S z i).mpr (mem_filter.mp ((mem_directions _ _ _).mp hi)).1

/-- If every realized two-axis contact mask is active, both banks retain all
their neighbors at a shared midpoint after freezing the inactive coordinates. -/
theorem shared_midpoint_neighbors_preserved
    {C D : Finset (Q 9)} {A : Finset (Fin 9)} {b : Bool} {z : Q 9}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hparC : ∀ x ∈ C, parity x = b)
    (hmask : ∀ T ∈ minimumDisplacements C D b 2, T ⊆ A)
    {i j : Fin 9} (hi : flip z i ∈ C) (hj : flip z j ∈ D) :
    directions C z = directions (restrictToFibre C A z) z ∧
      directions D z = directions (restrictToFibre D A z) z := by
  have hCactive : directions C z ⊆ A := by
    intro k hk
    exact (cross_pair_axes_active hsep hparC hmask
      ((mem_directions C z k).mp hk) hj).1
  have hDactive : directions D z ⊆ A := by
    intro k hk
    exact (cross_pair_axes_active hsep hparC hmask hi
      ((mem_directions D z k).mp hk)).2
  exact ⟨directions_restrictToFibre_eq hCactive,
    directions_restrictToFibre_eq hDactive⟩

#print axioms shared_midpoint_neighbors_preserved

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9InactiveContactFibre
