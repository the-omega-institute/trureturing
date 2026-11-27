/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33CompletionInputs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Two-coordinate saturation forces a corner and ambient packing forces sixty vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFiftyFourLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentWeightedProfile
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9Gray54ExtensionBound

/-! Size and direction-pair conditions for completing a contact rectangle. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33CompletionInputs

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip directionEdges direction_edge_count)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9ComponentSaturation (componentDefect)
open Q9ComponentWeightedProfile (exists_weighted_row_of_componentDefect_det_eq_zero)
open TwoBalancedComponents (componentFinset componentFinset_subset)
open private componentFinset_nonempty componentFinset_neighbor_closed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

open Classical in
/-- Two nonzero coordinate weights force a corner using both directions. -/
theorem exists_corner_for_each_direction_pair
    {U : Finset (Q 9)} {C : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent}
    (hdet : ∀ w : Fin 9 → ℝ, (componentDefect w U false C).det = 0)
    {i j : Fin 9} (hij : i ≠ j) :
    ∃ x ∈ componentFinset U C,
      flip x i ∈ componentFinset U C ∧ flip x j ∈ componentFinset U C := by
  let w : Fin 9 → ℝ := fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)
  have hw (k : Fin 9) : 0 ≤ w k := by
    dsimp only [w]
    split <;> split <;> norm_num
  have hsq (k : Fin 9) : w k ^ 2 = w k := by
    by_cases hi : k = i
    · subst k
      simp [w, hij]
    · by_cases hj : k = j <;> simp [w, hi, hj, hij.symm]
  have hsum (S : Finset (Fin 9)) :
      ∑ k ∈ S, w k = (if i ∈ S then 1 else 0) + (if j ∈ S then 1 else 0) := by
    simp only [w, sum_add_distrib, sum_ite_eq']
  obtain ⟨x, hx, hrow⟩ := exists_weighted_row_of_componentDefect_det_eq_zero
    U false C w hw (hdet w)
  have hs : (∑ k, w k ^ 2) = 2 := by
    simp only [hsq]
    norm_num [hsum]
  rw [hs, hsum] at hrow
  have hval : 1 < Real.sqrt (2 : ℝ) := by norm_num [Real.lt_sqrt]
  have hi : i ∈ directions (componentFinset U C) x := by
    by_contra hn
    rw [ite_eq_right hn, zero_add] at hrow
    split at hrow <;> linarith
  have hj : j ∈ directions (componentFinset U C) x := by
    by_contra hn
    rw [ite_eq_right hn, add_zero] at hrow
    split at hrow <;> linarith
  exact ⟨x, hx, (mem_directions _ _ _).mp hi, (mem_directions _ _ _).mp hj⟩

open Classical in
/-- A balanced cubic component in a 258-vertex candidate has
at least 60 vertices. The 54-vertex extremizer admits only 257 vertices in
the ambient set, and every balanced cubic size is a multiple of six. -/
theorem sixty_le_actual_component
    {U : Finset (Q 9)} (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    (hr : ((hypercube 9).induce (componentFinset U K : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced (componentFinset U K)) :
    60 ≤ (componentFinset U K).card := by
  let C := componentFinset U K
  have h54 : 54 ≤ C.card := by
    by_contra! hs
    exact BalancedCubeFiftyFourLowerBound.result
      ⟨C, componentFinset_nonempty U K, hr, hb, hs⟩
  have hn54 : C.card ≠ 54 := by
    intro hs
    have hc := Q9Gray54ExtensionBound.card_le_of_balanced_cubic_fifty_four
      U C hs hr hb (componentFinset_subset U K)
      (fun x hx y hy hadj => componentFinset_neighbor_closed U K x hx y hy hadj) hdeg
    omega
  have hdiv : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  change 60 ≤ C.card
  omega

#print axioms exists_corner_for_each_direction_pair
#print axioms sixty_le_actual_component

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33CompletionInputs
