/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoTenMasks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceTwoTenMasks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: In any 258-vertex subcubic induced candidate, the actual saturated pair realizes at least ten masks on each parity for which a distance-two contact occurs. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NineMaskExclusion

/-! A candidate pair needs ten contact masks on each nonempty starting parity. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceTwoTenMasks

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open CubicContactDistance (closest_pair_distance_add_five_le)
open TwoBalancedComponents (componentFinset componentFinset_subset)
open Translation.Q9ActualAperiodicity
  (exists_two_aperiodic_components signed_defect_det_eq_component)
open Q9DistanceFourExclusion (no_distance_four_of_four_separated)
open Q9DistanceThreeExclusion (no_minimum_distance_three)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9TightDistanceTwoReplay (minimum_displacements_card_ne_six)
open Q9IsotropicHuang (parity weightedLinear)
open Q9WeightedSaturation (defect signedBiadjacency)
open private componentFinset_nonempty componentFinset_disjoint componentFinset_neighbor_closed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
open private component_connected from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open private minimum_displacements_three_extensions mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open Q9EightMaskReplay (minimum_displacements_card_ne_eight)
open Q9EightMaskGraph (eight_le_of_three_extensions_of_card_ne_six)

open Q9NineMaskExclusion (no_nine_masks_in_actual_pair)

open Classical in
/-- Any 258-vertex subcubic candidate has a pair of components at minimum
distance two with at least ten masks on each nonempty starting parity. -/
theorem exists_actual_pair_with_ten_masks
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)),
      ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      K ≠ L ∧
      let C := componentFinset U K
      let D := componentFinset U L
      (∃ x ∈ C, ∃ y ∈ D, hammingDist x y = 2) ∧
        (∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y) ∧
        ∀ b, (minimumDisplacements C D b 2).Nonempty →
          10 ≤ (minimumDisplacements C D b 2).card := by
  obtain ⟨K, L, hKL, hcomponents⟩ := exists_two_aperiodic_components U hU hdeg
  let C := componentFinset U K
  let D := componentFinset U L
  obtain ⟨hrC, hbC, hsC, _⟩ := hcomponents K (Or.inl rfl)
  obtain ⟨hrD, hbD, hsD, _⟩ := hcomponents L (Or.inr rfl)
  have hcC := component_connected U K
  have hcD := component_connected U L
  have hdetC (w : Fin 9 → ℝ) : (defect w (signedBiadjacency w C false)).det = 0 :=
    (signed_defect_det_eq_component w U false K).trans (hsC w)
  have hdetD (w : Fin 9 → ℝ) : (defect w (signedBiadjacency w D false)).det = 0 :=
    (signed_defect_det_eq_component w U false L).trans (hsD w)
  have hC : C.Nonempty := componentFinset_nonempty U K
  have hD : D.Nonempty := componentFinset_nonempty U L
  have hdis : Disjoint C D := componentFinset_disjoint U K L hKL
  have hclosedC := componentFinset_neighbor_closed U K
  have hclosedD := componentFinset_neighbor_closed U L
  have hnC : 48 ≤ C.card := BalancedCubeLowerBound.forty_eight_le_card C hC hrC hbC
  have hnD : 48 ≤ D.card := BalancedCubeLowerBound.forty_eight_le_card D hD hrD hbD
  obtain ⟨⟨x, y⟩, hxy, hmin⟩ := exists_min_image (C.product D)
    (fun p => hammingDist p.1 p.2) (hC.product hD)
  obtain ⟨hx, hy⟩ := mem_product.mp hxy
  have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
      hammingDist x y ≤ hammingDist u v := hmin (u, v) (mem_product.mpr ⟨hu, hv⟩)
  have hzero : hammingDist x y ≠ 0 := fun hz =>
    disjoint_left.mp hdis ((hammingDist_eq_zero.mp hz) ▸ hx) hy
  have hone : hammingDist x y ≠ 1 := fun ho =>
    disjoint_left.mp hdis (hclosedC x hx y (componentFinset_subset U L hy) ho) hy
  have hhigh : hammingDist x y + 5 ≤ 9 := closest_pair_distance_add_five_le hrC hrD hbC hx hy hm
  have hfour : hammingDist x y ≠ 4 := fun hd =>
    no_distance_four_of_four_separated hrC hrD hbC hbD
      (fun u hu v hv => hd ▸ hm u hu v hv) hx hy hd
  have hthree : hammingDist x y ≠ 3 := fun hd =>
    no_minimum_distance_three U hU hdeg hrC hrD hbC hbD hnC hnD hclosedC hclosedD
      (fun u hu v hv => hd ▸ hm u hu v hv) hx hy hd
  have heq : hammingDist x y = 2 := by omega
  have hsep (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
      2 ≤ hammingDist u v := heq ▸ hm u hu v hv
  refine ⟨K, L, hKL, ⟨x, hx, y, hy, heq⟩, hsep, ?_⟩
  intro b hb
  have hne := minimum_displacements_card_ne_six (b := b) hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  let F := minimumDisplacements C D b 2
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨x', _, y', _, _, hdist, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hdist
  have hthree := minimum_displacements_three_extensions C D b 2 hsep
    (fun i => by
      let w : Fin 9 → ℝ := fun k => if k = i then 2 else 1
      have hw (k : Fin 9) : 0 < w k := by
        dsimp only [w]
        split <;> norm_num
      exact exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b)
    (fun c => exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD
      (fun _ => 1) (fun _ => by norm_num) (hdetD fun _ => 1) c)
  have he : 8 ≤ F.card :=
    eight_le_of_three_extensions_of_card_ne_six F hb hsize hthree hne
  have hneEight := minimum_displacements_card_ne_eight (b := b) hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  change F.card ≠ 8 at hneEight
  have hneNine := no_nine_masks_in_actual_pair (b := b)
    hU hdeg K L hsep hrC hrD hbC hbD hsC hsD
  change F.card ≠ 9 at hneNine
  change 10 ≤ F.card
  omega

#print axioms exists_actual_pair_with_ten_masks

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceTwoTenMasks
