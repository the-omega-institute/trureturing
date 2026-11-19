import D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import Batteries.Tactic.OpenPrivate

/-! Degree separation in a twenty-vertex literal half of a balanced cubic
support of order seventy-two. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoThinSlice

attribute [local instance] Classical.propDecidable

open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree)
open private coordinate_slice_degree_cases coordinate_slice_low_independent low_slice_card_eq_q
  parts_card from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private highWithHigh high_neighbor_deficit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice

/-- A twenty-vertex half has twelve cut endpoints and eight cubic vertices.
Every edge joins different degree classes, so suppressing the degree-two
vertices uses every edge of the half. -/
theorem degree_classes {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
    (degreeTwo G Finset.univ).card = 12 ∧ (degreeThree G Finset.univ).card = 8 ∧
      ∀ {v w}, G.Adj v w →
        (G.degree v = 2 ∧ G.degree w = 3) ∨ (G.degree v = 3 ∧ G.degree w = 2) := by
  classical
  let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 :=
    fun v => coordinate_slice_degree_cases v.property hr
  have hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False :=
    fun hxy hx hy => coordinate_slice_low_independent hr hb hxy hx hy
  have hcut : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hlo : (degreeTwo G Finset.univ).card = 12 := by
    calc
      _ = directionEdges C 0 := low_slice_card_eq_q hr
      _ = 12 := by omega
  have htotal := parts_card G hdeg Finset.univ
  have hsize : Fintype.card (coordinateSlice C b : Set (Q 9)) = 20 := by
    simpa using hs
  rw [Finset.card_univ, hsize, hlo] at htotal
  have hhi : (degreeThree G Finset.univ).card = 8 := by omega
  have hdeficit := high_neighbor_deficit G hdeg hlow
  rw [hlo, hhi] at hdeficit
  have hnone : highWithHigh G = ∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨hlo, hhi, ?_⟩
  intro v w hAdj
  rcases hdeg v with hv | hv <;> rcases hdeg w with hw | hw
  · exact (hlow hAdj hv hw).elim
  · exact Or.inl ⟨hv, hw⟩
  · exact Or.inr ⟨hv, hw⟩
  · have hmem : v ∈ highWithHigh G :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, w, hAdj, hw⟩
    simp [hnone] at hmem

#print axioms degree_classes

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoThinSlice
