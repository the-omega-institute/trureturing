/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SaturatedLargePairContacts
   generality: I
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Bounds distance-two contacts between separated balanced cubic Q9 supports. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SaturatedContactBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SmallComponentBoundary142
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyHalfExclusion

/-! The thin-half exclusion supplies the exterior-boundary bound for the smaller support. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SaturatedLargePairContacts

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9BoundaryEdgeTranslations (boundary)
open Q9MixedBoundaryCollisions (Separated)
open Q9MixedCollisionEnergyBound (distanceTwoPairs)
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
open private separated_union_regular from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions
open private mem_boundary_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9CommonBoundaryObstruction
open private mem_openNeighborhood from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SmallComponentBoundary142
open private distanceTwoPairs_card_even distanceTwoPairs_card_ne_322 from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SaturatedContactBound

attribute [local instance] Classical.propDecidable

private theorem smaller_boundary_card_ge_142 {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hc : C.card = 72) (hd : D.card = 186) :
    142 ≤ (boundary C).card := by
  classical
  have hU : (C ∪ D).card = 258 := by
    rw [Finset.card_union_of_disjoint hsep.1, hc, hd]
  have hsub : C ⊆ C ∪ D := Finset.subset_union_left
  have hclosed : ∀ x ∈ C, ∀ y ∈ C ∪ D, (hypercube 9).Adj x y → y ∈ C := by
    intro x hx y hy hadj
    exact (Finset.mem_union.mp hy).resolve_right (fun hyD => hsep.2 x hx y hyD hadj)
  have hregular := separated_union_regular hsep hrC hrD
  have hdeg : ∀ x ∈ C ∪ D, ((C ∪ D).filter ((hypercube 9).Adj x)).card ≤ 3 := by
    intro x hx
    have hneighbors : (C ∪ D).filter ((hypercube 9).Adj x) =
        (hypercube 9).neighborFinset x ∩ (C ∪ D) := by
      ext y
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hneighbors, selected_neighbor_card hx, hregular.degree_eq ⟨x, hx⟩]
  have h20 := no_twenty_half hU hc hrC hbC hsub hclosed hdeg
  have hboundary : Q9SmallComponentBoundary142.exteriorBoundary C = boundary C := by
    ext y
    simp only [Q9SmallComponentBoundary142.exteriorBoundary, Finset.mem_sdiff,
      mem_openNeighborhood, mem_boundary_iff, and_comm]
  rw [← hboundary]
  exact Q9SmallComponentBoundary142.exteriorBoundary_card_ge_142_of_card_eq_72_of_no_twenty_half
    hc hrC hbC h20

/-- Separated balanced cubic supports of orders 72 and 186 in the nine-cube
have at least 322 ordered cross pairs at Hamming distance two. -/
theorem distanceTwoPairs_card_ge_322 {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hc : C.card = 72) (hd : D.card = 186) :
    322 ≤ (distanceTwoPairs C D).card :=
  Q9SaturatedContactBound.distanceTwoPairs_card_ge_322 hsep hrC hrD hbC hbD hc hd
    (smaller_boundary_card_ge_142 hsep hrC hrD hbC hc hd)

/-- Separated balanced cubic supports of orders 72 and 186 in the nine-cube
have at least 324 ordered cross pairs at Hamming distance two. -/
theorem distanceTwoPairs_card_ge_324 {C D : Finset (Q 9)} (hsep : Separated C D)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) (hc : C.card = 72) (hd : D.card = 186) :
    324 ≤ (distanceTwoPairs C D).card := by
  have hlo := distanceTwoPairs_card_ge_322 hsep hrC hrD hbC hbD hc hd
  have hne := distanceTwoPairs_card_ne_322 hsep hrC hrD hbC hbD hc hd
    (smaller_boundary_card_ge_142 hsep hrC hrD hbC hc hd)
  obtain ⟨k, hk⟩ := distanceTwoPairs_card_even hsep hrC hrD hbC hbD
  omega

#print axioms distanceTwoPairs_card_ge_322
#print axioms distanceTwoPairs_card_ge_324

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SaturatedLargePairContacts
