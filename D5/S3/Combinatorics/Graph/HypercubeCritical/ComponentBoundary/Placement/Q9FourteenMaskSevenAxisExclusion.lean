import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenMaskSevenAxisClassification
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FifteenMaskLargeAxesActual
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case463F7E7677
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46435A7E77
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46437A7677
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46437E766F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46437E7657
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case4645687E77
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46456A7E6F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46457A6677
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46457A766F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46457A7667
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46457A6E6F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46456E6677
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46456E766F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46456E7667
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46456E7657
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46456C7E6F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46467A666F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46516A7677
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46517A5677
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46517A766F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46517A7667
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46517A5E6F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46555A766F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46555A7657
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46555A7577
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case465578766F
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FourteenAxes7Case46557A726F

/-! The contact-graph isomorphism labels the seven active axes of an actual
component pair. Extend it over the two unused labels to a permutation of all
nine coordinates. The image of the recipe edge `{0, 1}` supplies a realized
contact for rooting. The existing coordinate action then puts the pair in
the canonical form of the typed replay.

This uses the seven-axis classifier's isomorphism from `recipeGraph kind` to
the actual graph. The recipe vertices are bit indices 0 through 6, and its
edges are the pairs in `(recipe (maskWords kind)).family`. Each `maskWords`
entry uses the same ordered list as its indexed replay. -/

set_option autoImplicit false
set_option maxRecDepth 50000

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
namespace Q9FourteenMaskSevenAxisExclusion

open Finset
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeComponentBoundary (regular_directions exterior_even)
open BalancedCubeGirth (no_selected_square)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open Q9FifteenMaskLargeAxesReplay (Inputs recipe)
open Q9FourteenMaskSevenAxisClassification
  (Vertex fourteen_edges_on_seven_vertices maskWords recipeFamily recipeGraph recipeGraph_adj)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9SharedContactCNF (Axis)
open Q9SharedContactNormalized (LocalRules)
open Q9SquareMaskGraph (activeAxes maskGraph card_edges distance_two_mask_graph_constraints)
open Q9WeightedSaturation (defect signedBiadjacency)
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private mem_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
open private extend_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TenMaskRootNormalization

open Classical in
/-- The geometric laws of the actual pair give an isomorphism from an audited
seven-axis recipe to its contact graph. -/
theorem classify_contact_graph {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 7)
    (hcard : (minimumDisplacements C D b 2).card = 14) :
    ∃ kind : Fin 27, Nonempty (recipeGraph kind ≃g maskGraph (minimumDisplacements C D b 2)) := by
  let F := minimumDisplacements C D b 2
  let G := maskGraph F
  have hsize (T : Finset Axis) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨_, _, _, _, _, ht, rfl⟩ := mem_minimumDisplacements.mp hT
    exact ht
  have hV : Fintype.card (activeAxes F) = 7 := (Fintype.card_coe _).trans haxes
  have hE : G.edgeFinset.card = 14 := (card_edges F hsize).trans hcard
  obtain ⟨hmin, hsq⟩ := distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  have localRules {S : Finset (Q 9)}
      (hr : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
      (hb : IsBalanced S) : LocalRules S :=
    ⟨fun _ hs => regular_directions S hr hs, exterior_even S hr hb,
      fun _ _ _ hij hs hi hj hs' => no_selected_square hb hij hs hi hj hs'⟩
  apply fourteen_edges_on_seven_vertices G hV hE hmin
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a v c
    exact hsq
  · intro a v c hav ha hv hac hvc
    exact Q9ContactGraphTriangles.cubic_edge_common_neighbor_has_companion (b := b)
      hsep hrC hrD hcC hcD hbC hbD hdetC hdetD hav ha hv hac hvc
  · exact Q9CubicTriangleExclusion.no_cubic_contact_triangle (b := b)
      hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  · intro a c hac
    obtain ⟨p, q, hpa, hqc, hpc, hqa, hpq, hp, hq, hpq'⟩ :=
      Q9EveryContactEdgeSquare.every_realized_mask_on_four_cycle
        (localRules hrC hbC) (localRules hrD hbD) hsep hac.2
    let x : activeAxes F := ⟨p, mem_axes.mpr ⟨_, hp, by simp⟩⟩
    let y : activeAxes F := ⟨q, mem_axes.mpr ⟨_, hq, by simp⟩⟩
    refine ⟨y, ?_, ?_, x, ?_, ?_, ?_⟩
    · exact ⟨fun he => hqa (congrArg Subtype.val he).symm, hq⟩
    · exact fun he => hqc (congrArg Subtype.val he)
    · exact fun he => hpa (congrArg Subtype.val he)
    · refine ⟨fun he => hpc (congrArg Subtype.val he).symm, ?_⟩
      change ({c.val, p} : Finset Axis) ∈ F
      rw [Finset.pair_comm]
      exact hp
    · refine ⟨fun he => hpq (congrArg Subtype.val he).symm, ?_⟩
      change ({q, p} : Finset Axis) ∈ F
      rw [Finset.pair_comm]
      exact hpq'

private abbrev lowAxis : Vertex ↪ Axis := Fin.castLEEmb (by decide)

private theorem family_card (kind : Fin 27) : (recipeFamily kind).card = 14 := by
  fin_cases kind <;> decide +kernel

set_option maxHeartbeats 2000000 in
private theorem family_shape (kind : Fin 27) :
    ∀ T ∈ recipeFamily kind, T.card = 2 ∧ ∀ a ∈ T, a.val < 7 := by
  fin_cases kind <;> decide +kernel

private theorem root_edge (kind : Fin 27) : (recipeGraph kind).Adj 0 1 := by
  fin_cases kind <;> decide +kernel

set_option maxHeartbeats 1000000 in
open Classical in
/-- Transport the actual pair to rooted inputs for its indexed recipe. -/
theorem exists_replay_inputs {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hsC : 60 ≤ C.card) (hsD : 60 ≤ D.card)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 7)
    (hcard : (minimumDisplacements C D b 2).card = 14) :
    ∃ kind : Fin 27, ∃ X Y, Inputs (recipe (maskWords kind)) X Y := by
  let F := minimumDisplacements C D b 2
  obtain ⟨kind, ⟨e⟩⟩ := classify_contact_graph
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD haxes hcard
  let labels : Vertex ↪ Axis :=
    { toFun := fun i => (e i).val
      inj' := fun _ _ h => e.toEquiv.injective (Subtype.ext h) }
  obtain ⟨σ, hσ⟩ := extend_axes (by decide : 7 ≤ 9) labels
  have hmask {i j : Vertex} (h : (recipeGraph kind).Adj i j) :
      ({σ (lowAxis i), σ (lowAxis j)} : Finset Axis) ∈ F := by
    rw [hσ i, hσ j]
    exact (e.map_adj_iff.mpr h).2
  have hM : ∀ T ∈ recipeFamily kind, T.map σ.toEmbedding ∈ F := by
    intro T hT
    obtain ⟨hsize, hs⟩ := family_shape kind T hT
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hsize
    let i' : Vertex := ⟨i.val, hs i (by simp)⟩
    let j' : Vertex := ⟨j.val, hs j (by simp)⟩
    have hi : lowAxis i' = i := Fin.ext rfl
    have hj : lowAxis j' = j := Fin.ext rfl
    have hij' : i' ≠ j' :=
      fun he => hij (hi.symm.trans ((congrArg (fun a : Vertex => lowAxis a) he).trans hj))
    have hadj : (recipeGraph kind).Adj i' j' := by
      apply (recipeGraph_adj kind i' j').mpr
      refine ⟨hij', ?_⟩
      change ({lowAxis i', lowAxis j'} : Finset Axis) ∈ recipeFamily kind
      simpa only [hi, hj] using hT
    simpa only [hi, hj, map_insert, map_singleton, Equiv.coe_toEmbedding] using hmask hadj
  have hn : (recipeFamily kind).card = F.card := (family_card kind).trans hcard.symm
  exact ⟨kind, Q9FifteenMaskLargeAxesActual.exists_rooted_inputs_of_labeling
    (recipe (maskWords kind)) Subset.rfl σ (hmask (root_edge kind)) hM hn hsep
    hrC hrD hcC hcD hbC hbD hdetC hdetD hsC hsD⟩

open Classical in
/-- No saturated cubic component pair of size at least sixty realizes a
fourteen-mask family with seven active axes. -/
theorem no_fourteen_masks_on_seven_axes {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hsC : 60 ≤ C.card) (hsD : 60 ≤ D.card)
    (haxes : (activeAxes (minimumDisplacements C D b 2)).card = 7)
    (hcard : (minimumDisplacements C D b 2).card = 14) : False := by
  obtain ⟨kind, X, Y, h⟩ := exists_replay_inputs
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD hsC hsD haxes hcard
  fin_cases kind
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible0 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible1 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible2 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible3 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible4 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible5 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible6 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible7 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible8 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible9 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible10 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible11 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible12 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible13 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible14 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible15 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible16 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible17 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible18 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible19 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible20 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible21 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible22 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible23 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible24 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible25 X Y h
  · exact Q9FifteenMaskLargeAxesReplay.fourteenSevenImpossible26 X Y h

#print axioms no_fourteen_masks_on_seven_axes

end Q9FourteenMaskSevenAxisExclusion
end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement
