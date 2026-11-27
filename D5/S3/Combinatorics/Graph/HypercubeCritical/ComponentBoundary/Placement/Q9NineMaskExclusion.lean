/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9NineMaskExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9NineMaskExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Five active coordinates give the six normalized orbits. Six active coordinates give the complete bipartite contact graph and its two aligned parity rectangles. Both branches are excluded. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NormalizeNineMasks
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitZero
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitTwo
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitThree
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitFour
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitFive
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisSharedFace
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33SmallSupportReplay
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9DistanceTwoNineMasks

/-! Nine contact masks are incompatible with two actual components of a candidate. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NineMaskExclusion

open Finset
open BalancedCriticalSpectrum (Q IsBalanced)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open Q9IsotropicHuang (parity)
open Q9FiveAxisOrbitCover (Pattern Word representatives orbit)
open Q9FiveAxisInputClauses (Inputs)
open private balanced_at from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisInputClauses
open private mem_evenWords_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitGeometry
open Q9FiveAxisRepresentative (exists_signed_representative)
open Q9FiveAxisSharedFace (no_second_orbit)
open Q9FiveAxisLayerAction (LayerMatches)
open Q9SquareMaskGraph (activeAxes distance_two_mask_graph_constraints)
open Q9NormalizeNineMasks (six_axes_or_delete_one)
open Q9MinimumDistanceOperator (minimumDisplacements)
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private mem_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount
open TwoBalancedComponents (componentFinset)
open Translation.Q9ActualAperiodicity (signed_defect_det_eq_component)
open private component_connected from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9TranslationAperiodicity
open Q9ComponentSaturation (componentDefect)

private theorem impossible_representative {C D : Finset (Q 9)} {f : Bool → Q 9 → ℤ} {r : Pattern}
    (hr : r ∈ representatives) (h : Inputs C D f r) : False := by
  have hs : ∀ p ∈ representatives, p = representatives[0]! ∨ p = representatives[1]! ∨
      p = representatives[2]! ∨ p = representatives[3]! ∨ p = representatives[4]! ∨
      p = representatives[5]! := by decide +kernel
  rcases hs r hr with h0 | h1 | h2 | h3 | h4 | h5
  · subst r
    exact Q9FiveAxisOrbitZero.impossible C D f h
  · subst r
    apply no_second_orbit (p := representatives[1]!) (by decide +kernel) _
      h.geom.separated h.counts (h.regular false) (balanced_at h false)
    intro s w hw hp
    exact h.layer s w ((mem_evenWords_iff w).mpr ⟨hw, hp⟩)
  · subst r
    exact Q9FiveAxisOrbitTwo.impossible C D f h
  · subst r
    exact Q9FiveAxisOrbitThree.impossible C D f h
  · subst r
    exact Q9FiveAxisOrbitFour.impossible C D f h
  · subst r
    exact Q9FiveAxisOrbitFive.impossible C D f h

open Classical in
/-- An actual separated saturated pair in a 258-vertex candidate cannot have nine
distance-two masks on either parity. The degree sum bounds the mask graph to six
axes and the number of pairs needs five axes. Each case gives a contradiction. -/
theorem no_nine_masks_in_actual_pair
    {U : Finset (Q 9)} (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (K L : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent)
    {b : Bool}
    (hsep : ∀ x ∈ componentFinset U K, ∀ y ∈ componentFinset U L, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (componentFinset U K : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (componentFinset U L : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced (componentFinset U K)) (hbD : IsBalanced (componentFinset U L))
    (hdetC : ∀ w : Fin 9 → ℝ, (componentDefect w U false K).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (componentDefect w U false L).det = 0) :
    (minimumDisplacements (componentFinset U K) (componentFinset U L) b 2).card ≠ 9 := by
  intro hnine
  let F := minimumDisplacements (componentFinset U K) (componentFinset U L) b 2
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨_, _, _, _, _, hd, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hd
  have hcC := component_connected U K
  have hcD := component_connected U L
  have hsC (w : Fin 9 → ℝ) := (signed_defect_det_eq_component w U false K).trans (hdetC w)
  have hsD (w : Fin 9 → ℝ) := (signed_defect_det_eq_component w U false L).trans (hdetD w)
  have hmin := (distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hsC hsD).1
  rcases six_axes_or_delete_one F hnine hsize hmin with hsix | ⟨_, _, hfive, _⟩
  · exact Q9K33SmallSupportReplay.no_nine_masks_on_six_axes_in_actual_pair
      hU hdeg K L hsep hrC hrD hbC hbD hdetC hdetD hsix hnine
  · have hcontained (T : Finset (Fin 9)) (hT : T ∈ F) : T ⊆ activeAxes F :=
      fun i hi => mem_axes.mpr ⟨T, hT, hi⟩
    obtain ⟨X, Y, f, r, hr, hm, hg, hf, hc, ht, hr', hs⟩ :=
      exists_signed_representative hfive hnine hcontained hsep hrC hrD hcC hcD hbC hbD hsC hsD
    exact impossible_representative hr ⟨hg, hf, hm, hc, ht, hr', hs⟩

#print axioms no_nine_masks_in_actual_pair

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9NineMaskExclusion
