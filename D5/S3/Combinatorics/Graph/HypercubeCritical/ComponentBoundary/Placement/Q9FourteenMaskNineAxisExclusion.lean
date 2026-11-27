/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FourteenMaskNineAxisExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FourteenMaskNineAxisExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: The nine-axis contact graph cannot have exactly fourteen edges. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactGraphTriangles
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenMaskGraph

/-! A distance-two mask family with fourteen masks cannot use all nine axes. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9FourteenMaskNineAxisExclusion

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SquareMaskGraph (activeAxes maskGraph card_edges distance_two_mask_graph_constraints)
open Q9ContactGraphTriangles (cubic_edge_common_neighbor_has_companion)
open Q9FourteenMaskGraph (fourteen_edges_on_nine_vertices_impossible)
open Q9WeightedSaturation (defect signedBiadjacency)
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator

open Classical in
/-- The local constraints from cubic component geometry exclude the first
possible mask cardinality using all nine axes. -/
theorem no_fourteen_masks_on_nine_axes
    {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 9) :
    (minimumDisplacements C D b 2).card ≠ 14 := by
  let F := minimumDisplacements C D b 2
  intro hcard
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨_, _, _, _, _, ht, rfl⟩ := mem_minimumDisplacements.mp hT
    exact ht
  have hV : Fintype.card (activeAxes F) = 9 := (Fintype.card_coe _).trans haxes
  have hE : (maskGraph F).edgeFinset.card = 14 := (card_edges F hsize).trans hcard
  have hshape := distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  apply fourteen_edges_on_nine_vertices_impossible (maskGraph F) hV hE hshape.1
  · intro a v c hav hac hvc ha hv
    exact hshape.2 hav hac hvc ha hv
  · intro a v c hav ha hv hac hvc
    exact cubic_edge_common_neighbor_has_companion (b := b)
      hsep hrC hrD hcC hcD hbC hbD hdetC hdetD hav ha hv hac hvc

#print axioms no_fourteen_masks_on_nine_axes

end Q9FourteenMaskNineAxisExclusion
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
