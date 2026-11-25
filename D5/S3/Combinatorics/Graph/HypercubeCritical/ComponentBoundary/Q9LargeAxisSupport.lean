/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LargeAxisSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LargeAxisSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The smaller singular component in a hypothetical 258-set has large positive blocks on at least six axes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositiveSpectrumApplication
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9EightStarFootprintPacking

/-!
# Large positive boundary blocks on many axes

For Hong–Wu–Xia, arXiv:2610.09483v1, §7, Problem 2. The two fixed
universally singular cubic components are disjoint. The smaller has order
at most 126 by its direction count divisibility. Its eight-column blocks
are full stars, and each such direction requires a disjoint footprint of
32 actual vertices. Thus at least six distinct coordinate directions
admit a positive, universally singular block with nine or more columns.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LargeAxisSupport

open scoped Matrix
open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsSwitching directionEdges direction_edge_count)
open TwoBalancedComponents (componentFinset componentFinset_subset)
open Q9PositivePairedKernel (pairedGraph pairedVertex)
open Q9PositiveSpectrumApplication (componentColumns projectedOccupied
  exists_two_components_with_positive_spectrum_bound)
open CoordinateHalves.Q9DominantAxisBoundary (PairedRows emptyFibreBoundary)
open Q9TwoStarAxisBound (EightStar eightStar_of_projected_certificate)
open Q9EightStarFootprintPacking (card_star_axes_le_three)
open private column_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9PositiveSpectrumApplication
open private componentFinset_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
open private liftVertex from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9OccupiedFibreParity

attribute [local instance] Classical.propDecidable

/-- A hypothetical 258-set has a cubic, universally singular component of
order at most 126 with at least six axes supporting nine or more columns
in one fixed occupied-connected weighted kernel block. -/
theorem exists_small_component_with_six_large_axes
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      let C := componentFinset U K
      C.card ≤ 126 ∧ ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
      ∃ σ : Q 9 → ℝ, IsSwitching C σ ∧ ∃ J : Finset (Fin 9), 6 ≤ J.card ∧
        ∀ i ∈ J, ∃ k : (pairedGraph C false i).ConnectedComponent,
          9 ≤ (componentColumns C false i k).card ∧
          ∀ w : Fin 9 → ℝ, ∃ f : PairedRows C false i → ℝ,
            f ≠ 0 ∧ emptyFibreBoundary C false i w *ᵥ f = 0 ∧
            (∀ x, (pairedGraph C false i).connectedComponentMk x ≠ k → f x = 0) ∧
            ((∀ a, a ≠ i → 0 < w a) →
              ∀ x, (pairedGraph C false i).connectedComponentMk x = k →
                0 < σ (pairedVertex x) * f x) := by
  obtain ⟨A, B, hAB, hcomponents⟩ := exists_two_components_with_positive_spectrum_bound U hU hdeg
  have hdisj := componentFinset_disjoint U A B hAB
  have hunion : componentFinset U A ∪ componentFinset U B ⊆ U :=
    union_subset (componentFinset_subset U A) (componentFinset_subset U B)
  have htotal := card_le_card hunion
  rw [card_union_of_disjoint hdisj, hU] at htotal
  have hsmall : ∃ K, (K = A ∨ K = B) ∧ (componentFinset U K).card ≤ 129 := by
    by_cases ha : (componentFinset U A).card ≤ 129
    · exact ⟨A, Or.inl rfl, ha⟩
    · exact ⟨B, Or.inr rfl, by omega⟩
  obtain ⟨K, hK, hbound⟩ := hsmall
  let C := componentFinset U K
  obtain ⟨hr, σ, hs, haxes⟩ := hcomponents K hK
  have hsize : 6 * directionEdges C 0 = C.card := direction_edge_count (d := 3) C hr ⟨σ, hs⟩ 0
  change C.card ≤ 129 at hbound
  have h126 : C.card ≤ 126 := by omega
  have hblocks : ∀ i : Fin 9, ∃ k : (pairedGraph C false i).ConnectedComponent,
      8 ≤ (componentColumns C false i k).card ∧
      (∀ w : Fin 9 → ℝ, ∃ f : PairedRows C false i → ℝ,
        f ≠ 0 ∧ emptyFibreBoundary C false i w *ᵥ f = 0 ∧
        (∀ x, (pairedGraph C false i).connectedComponentMk x ≠ k → f x = 0) ∧
        ((∀ a, a ≠ i → 0 < w a) → ∀ x,
          (pairedGraph C false i).connectedComponentMk x = k → 0 < σ (pairedVertex x) * f x)) ∧
      ((componentColumns C false i k).card = 8 →
        ∃ (r : Q 9) (P R : Finset (Fin 9)), EightStar C i r P R) := by
    intro i
    obtain ⟨_, k, hk, hker, hstar⟩ := haxes i
    refine ⟨k, hk, hker, fun he => ?_⟩
    apply eightStar_of_projected_certificate (K := componentColumns C false i k)
      (occupied := projectedOccupied C i)
    · exact fun q hq t => column_pair hq t
    · intro q
      simp only [projectedOccupied, decide_eq_true_eq]
    · exact hstar he
  choose k hk hker hstar using hblocks
  let small := univ.filter (fun i : Fin 9 => (componentColumns C false i (k i)).card = 8)
  have hsmall : small.card ≤ 3 := by
    apply card_star_axes_le_three hr h126 small
    intro i hi
    exact hstar i (mem_filter.mp hi).2
  let large := univ \ small
  have hlarge : 6 ≤ large.card := by
    have hpart := card_sdiff_add_card_eq_card (show small ⊆ univ from subset_univ _)
    have h9 : (univ : Finset (Fin 9)).card = 9 := by simp
    change large.card + small.card = (univ : Finset (Fin 9)).card at hpart
    omega
  refine ⟨K, h126, hr, σ, hs, large, hlarge, ?_⟩
  intro i hi
  have hnot : i ∉ small := (mem_sdiff.mp hi).2
  have h8ne : (componentColumns C false i (k i)).card ≠ 8 :=
    fun he => hnot (mem_filter.mpr ⟨mem_univ _, he⟩)
  refine ⟨k i, ?_, hker i⟩
  change 9 ≤ (componentColumns C false i (k i)).card
  have := hk i
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LargeAxisSupport
