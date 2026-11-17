/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ThinCoordinateSlice
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ThinCoordinateSlice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: A nonempty Huang-balanced induced cubic Q9 support with a coordinate-zero half of size at most sixteen has size54 and that half is a fifteen-vertex K3,3 subdivision. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.FifteenSliceStructure
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFiftyFourLowerBound
import Batteries.Tactic.OpenPrivate

/-! The original induced coordinate half inherits the hypotheses of the
fifteen-vertex incidence classification. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ThinCoordinateSlice

open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open FifteenSliceStructure (IsK33Subdivision fifteen_vertex_subdivision)
open private coordinate_slice_degree_cases low_slice_card_eq_q
  coordinate_slice_low_independent balanced_subset paritySide parity_union parity_bipartite
  parts_card sum_degrees_parts twice_low_le_three_high from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

private theorem fifteen_of_nine_lows {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3)
    (hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False)
    (hq : (degreeTwo G Finset.univ).card = 9) (hN : Fintype.card V ≤ 16) :
    Fintype.card V = 15 := by
  have hp := parts_card G hdeg Finset.univ
  have hi := twice_low_le_three_high G hdeg hlow
  have hsum : 2 * (degreeTwo G Finset.univ).card +
      3 * (degreeThree G Finset.univ).card = 2 * G.edgeFinset.card := by
    rw [← sum_degrees_parts G hdeg Finset.univ]
    exact G.sum_degrees_eq_twice_card_edges
  rw [hq, Finset.card_univ] at hp
  rw [hq] at hi hsum
  omega

/-- The hypothesis concerns the actual coordinate-zero half of the original
balanced support, with its original induced adjacency. -/
theorem thin_coordinate_slice {C : Finset (Q 9)} (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card ≤ 16) :
    C.card = 54 ∧ (coordinateSlice C b).card = 15 ∧
      IsK33Subdivision ((hypercube 9).induce (coordinateSlice C b : Set (Q 9))) := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 := fun v =>
    coordinate_slice_degree_cases v.property hr
  have hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False := by
    intro v w hxy hx hy
    exact coordinate_slice_low_independent hr hb hxy hx hy
  have hbal : IsBalanced S := balanced_subset hb (Finset.filter_subset _ _)
  have hg : (8 : ℕ∞) ≤ G.egirth := BalancedCubeGirth.eight_le_egirth S hbal
  have hqcard : (degreeTwo G Finset.univ).card = directionEdges C 0 :=
    low_slice_card_eq_q hr
  have h54 : 54 ≤ C.card := by
    by_contra hn
    exact BalancedCubeFiftyFourLowerBound.result ⟨C, hC, hr, hb, by omega⟩
  have h6 : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hScard : Fintype.card (S : Set (Q 9)) = S.card := by simp
  have hN16 : Fintype.card (S : Set (Q 9)) ≤ 16 := by
    rw [hScard]
    exact hs
  have hp := parts_card G hdeg Finset.univ
  have hi := twice_low_le_three_high G hdeg hlow
  rw [hqcard, Finset.card_univ] at hp
  rw [hqcard] at hi
  have hq9 : directionEdges C 0 = 9 := by omega
  have hsize : C.card = 54 := by omega
  have hN15 : Fintype.card (S : Set (Q 9)) = 15 :=
    fifteen_of_nine_lows G hdeg hlow (hqcard.trans hq9) hN16
  refine ⟨hsize, ?_, ?_⟩
  · exact hScard.symm.trans hN15
  · exact fifteen_vertex_subdivision (parity_bipartite S) (parity_union S)
      hdeg hlow hg hN15 (hqcard.trans hq9)

#print axioms thin_coordinate_slice

end D5.S3.Combinatorics.Graph.HypercubeCritical.ThinCoordinateSlice
