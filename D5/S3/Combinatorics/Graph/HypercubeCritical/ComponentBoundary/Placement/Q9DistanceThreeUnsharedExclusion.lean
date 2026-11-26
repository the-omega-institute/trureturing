/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9DistanceThreeUnsharedExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: The omitted-edge budget excludes the all-unshared minimum-distance-three case. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ComplementBoundaryBudget
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeActiveBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeCrossingCount

/-! The complement edge budget excludes distance three when every closest pair
has disjoint occupied directions. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeUnsharedExclusion

open Finset
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced)
open BalancedCubeComponentBoundary (directions mem_directions)
open Q9ExteriorEdgeLiftCount (exterior exterior_edges_ge_one_hundred_four)
open Q9DistanceThreeActiveBoundary (active active_boundary_degrees)
open Q9ComplementBoundaryBudget (complement_darts_le packed_darts_le)
open Q9DistanceThreeCrossingCount (active_card_and_crossing_darts)

private theorem exterior_subset_complement_of_closed
    {C U : Finset (Q 9)}
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C) :
    exterior C ⊆ univ \ U := by
  classical
  intro z hz
  obtain ⟨hzC, i, hi⟩ : z ∉ C ∧ (directions C z).Nonempty := by
    simpa [exterior] using hz
  have hiC := (mem_directions C z i).mp hi
  exact mem_sdiff.mpr ⟨mem_univ _, fun hzU =>
    hzC (hclosed (flip z i) hiC z hzU ((hammingDist_comm (flip z i) z).trans (flip_adj z i)))⟩

private theorem exterior_disjoint_of_separation
    {C D : Finset (Q 9)} (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y) :
    Disjoint (exterior C) (exterior D) := by
  classical
  refine disjoint_left.mpr fun z hzC hzD => ?_
  obtain ⟨i, hi⟩ := (mem_filter.mp hzC).2
  obtain ⟨j, hj⟩ := (mem_filter.mp hzD).2
  have hlow := hsep (flip z i) ((mem_directions C z i).mp hi)
    (flip z j) ((mem_directions D z j).mp hj)
  have htri := hammingDist_triangle (flip z i) z (flip z j)
  rw [hammingDist_comm (flip z i) z, flip_adj z i, flip_adj z j] at htri
  omega

open Classical in
/-- Two closed balanced cubic supports in a 258-vertex subcubic restriction
cannot have minimum distance three with disjoint occupied directions at
every closest pair. -/
theorem no_unshared_distance_three
    (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    {C D : Finset (Q 9)}
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hnC : 48 ≤ C.card) (hnD : 48 ≤ D.card)
    (hclosedC : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hclosedD : ∀ x ∈ D, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ D)
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 3 ≤ hammingDist x y)
    (hdis : ∀ x ∈ C, ∀ y ∈ D, hammingDist x y = 3 →
      Disjoint (directions C x) (directions D y))
    {x y : Q 9} (hx : x ∈ C) (hy : y ∈ D) (hxy : hammingDist x y = 3) : False := by
  have hsep' (x : Q 9) (hx : x ∈ D) (y : Q 9) (hy : y ∈ C) : 3 ≤ hammingDist x y := by
    rw [hammingDist_comm]
    exact hsep y hy x hx
  have hdis' (x : Q 9) (hx : x ∈ D) (y : Q 9) (hy : y ∈ C) (hxy : hammingDist x y = 3) :
      Disjoint (directions D x) (directions C y) :=
    (hdis y hy x hx ((hammingDist_comm y x).trans hxy)).symm
  have haC x (hx : x ∈ active C D) := active_boundary_degrees hrC hrD hbC hsep hdis hx
  have haD x (hx : x ∈ active D C) := active_boundary_degrees hrD hrC hbD hsep' hdis' hx
  have hsubA (A B : Finset (Q 9)) : active A B ⊆ exterior A := filter_subset _ _
  have hcap := complement_darts_le U hU hdeg
  have hpack := packed_darts_le (exterior_subset_complement_of_closed hclosedC)
    (exterior_subset_complement_of_closed hclosedD) (exterior_disjoint_of_separation hsep)
  obtain ⟨hsizeC, hsizeD, hcross⟩ :=
    active_card_and_crossing_darts hrC hrD hbC hbD hsep hdis ⟨x, hx, y, hy, hxy⟩
      (fun x hx => (haC x hx).1) (fun x hx => (haD x hx).1)
  have hleft := exterior_edges_ge_one_hundred_four C hrC hbC hnC
    (active C D) hsizeC (hsubA C D) (fun x hx => (haC x hx).1) (fun x hx => (haC x hx).2)
  have hright := exterior_edges_ge_one_hundred_four D hrD hbD hnD
    (active D C) hsizeD (hsubA D C) (fun x hx => (haD x hx).1) (fun x hx => (haD x hx).2)
  omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceThreeUnsharedExclusion
