/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: In a hypothetical subcubic 258-vertex restriction of the nine-cube, the two balanced cubic components have minimum distance two. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeUnsharedExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactGeometryReplay
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceFourExclusion

/-! Every hypothetical 258-vertex subcubic support has balanced cubic
components at minimum distance two. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeExclusion

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeComponentBoundary (directions)
open TwoBalancedComponents (componentFinset exists_two_balanced_components)
open CubicContactDistance (closest_pair_distance_add_five_le)
open Q9DistanceFourExclusion (no_distance_four_of_four_separated)
open Q9DistanceThreeUnsharedExclusion (no_unshared_distance_three)
open Q9SharedContactGeometryReplay (no_shared_distance_three)

open Classical in
/-- The complement edge budget and the three shared-contact refutations
exclude all distance-three contacts between three-separated, closed balanced
cubic supports of size at least 48 in the proposed subcubic restriction. -/
theorem no_minimum_distance_three
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hnC : 48 ≤ C.card) (hnD : 48 ≤ D.card)
    (hclosedC : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hclosedD : ∀ x ∈ D, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y)
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D) (hxy : hammingDist x y = 3) : False := by
  apply no_unshared_distance_three U hU hdeg hrC hrD hbC hbD hnC hnD hclosedC hclosedD hsep _ hx hy hxy
  intro u hu v hv huv
  apply disjoint_left.mpr
  intro i hi hj
  exact no_shared_distance_three hrC hrD hbC hbD hsep hu hv huv ⟨i, mem_inter.mpr ⟨hi, hj⟩⟩

open Classical in
/-- Any 258-vertex induced subcubic subgraph in the nine-cube contains two
distinct balanced cubic components whose minimum distance is exactly two. -/
theorem exists_two_balanced_components_at_distance_two (U : Finset (Q 9))
    (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent,
      K ≠ L ∧ ∃ C D : Finset (Q 9),
        C = componentFinset U K ∧ D = componentFinset U L ∧
        ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
        ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3 ∧
        IsBalanced C ∧ IsBalanced D ∧
        ∃ x ∈ C, ∃ y ∈ D, hammingDist x y = 2 ∧
          ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v := by
  obtain ⟨K, L, hKL, C, D, hCK, hDL, hC, hD, _, hDU, hdis, hclosedC, hclosedD,
    hrC, hrD, hbC, hbD, hnC, hnD, _⟩ := exists_two_balanced_components U hU hdeg
  obtain ⟨⟨x, y⟩, hxy, hmin⟩ := exists_min_image (C.product D)
    (fun p => hammingDist p.1 p.2) (hC.product hD)
  obtain ⟨hx, hy⟩ := mem_product.mp hxy
  have hm (u : Q 9) (hu : u ∈ C) (v : Q 9) (hv : v ∈ D) :
      hammingDist x y ≤ hammingDist u v := hmin (u, v) (mem_product.mpr ⟨hu, hv⟩)
  have hzero : hammingDist x y ≠ 0 := fun hz =>
    disjoint_left.mp hdis ((hammingDist_eq_zero.mp hz) ▸ hx) hy
  have hone : hammingDist x y ≠ 1 := fun ho =>
    disjoint_left.mp hdis (hclosedC x hx y (hDU hy) ho) hy
  have hhigh : hammingDist x y + 5 ≤ 9 := closest_pair_distance_add_five_le hrC hrD hbC hx hy hm
  have hfour : hammingDist x y ≠ 4 := fun hd =>
    no_distance_four_of_four_separated hrC hrD hbC hbD
      (fun u hu v hv => hd ▸ hm u hu v hv) hx hy hd
  have hthree : hammingDist x y ≠ 3 := fun hd =>
    no_minimum_distance_three U hU hdeg hrC hrD hbC hbD hnC hnD hclosedC hclosedD
      (fun u hu v hv => hd ▸ hm u hu v hv) hx hy hd
  have heq : hammingDist x y = 2 := by omega
  exact ⟨K, L, hKL, C, D, hCK, hDL, hrC, hrD, hbC, hbD, x, hx, y, hy, heq,
    fun u hu v hv => heq ▸ hm u hu v hv⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeExclusion
