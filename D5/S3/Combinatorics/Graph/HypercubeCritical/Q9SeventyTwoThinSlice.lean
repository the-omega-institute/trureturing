import D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
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
  parts_card balanced_subset from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private highWithHigh high_neighbor_deficit from
  D5.S3.Combinatorics.Graph.HypercubeCritical.EighteenPointSlice
open private SideHigh compressed compressed_degree compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression

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

/-- Suppressing the twelve degree-two vertices yields a triangle-free cubic
graph on eight vertices, with every compressed edge realized in the half. -/
theorem compressed_cubic {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    let G := (hypercube 9).induce (coordinateSlice C b : Set (Q 9))
    ∃ (H : SimpleGraph (Fin 8)) (vertices : Fin 8 ↪ (coordinateSlice C b : Set (Q 9))),
      H.IsRegularOfDegree 3 ∧
      (∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) ∧
      ∀ x y, H.Adj x y ↔ x ≠ y ∧
        ∃ m, G.degree m = 2 ∧ G.Adj (vertices x) m ∧ G.Adj (vertices y) m := by
  classical
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := degreeThree G Finset.univ
  let R := degreeTwo G Finset.univ
  obtain ⟨_, hhi, hsplit⟩ := degree_classes hC hr hb b hs
  change ∀ {v w : (S : Set (Q 9))}, G.Adj v w →
    (G.degree v = 2 ∧ G.degree w = 3) ∨ (G.degree v = 3 ∧ G.degree w = 2) at hsplit
  have hpart : G.IsBipartiteWith (L : Set (S : Set (Q 9))) (R : Set (S : Set (Q 9))) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have h3 := (Finset.mem_filter.mp (show x ∈ L from hx)).2
      have h2 := (Finset.mem_filter.mp (show x ∈ R from hy)).2
      omega
    · intro x y hxy
      rcases hsplit hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
      · exact Or.inl ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 :=
    fun v => coordinate_slice_degree_cases v.property hr
  have hlow : ∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False :=
    fun hxy hx hy => coordinate_slice_low_independent hr hb hxy hx hy
  have hg : (8 : ℕ∞) ≤ G.egirth :=
    BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (Finset.filter_subset _ _))
  have hL : degreeThree G L = L := by
    ext v
    simp [L, degreeThree]
  have hcard : Fintype.card (SideHigh G L) = 8 := by
    change Fintype.card ↥(degreeThree G L) = 8
    rw [Fintype.card_coe, hL]
    exact hhi
  let label := (Fintype.equivFinOfCardEq hcard).symm
  let H := (compressed G L).comap label
  let vertices := label.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨H, vertices, ?_, ?_, ?_⟩
  · intro i
    have hdegree : (compressed G L).degree (label i) +
        (degreeThree G (G.neighborFinset (label i).val)).card = 3 :=
      compressed_degree hpart hdeg hlow hg (label i)
    have hnone : degreeThree G (G.neighborFinset (label i).val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨ha, hv3⟩ := Finset.mem_filter.mp hv
      have hi3 : G.degree (label i).val = 3 := (Finset.mem_filter.mp (label i).property).2
      rcases hsplit ((G.mem_neighborFinset _ _).mp ha) with ⟨h2, _⟩ | ⟨_, h2⟩
      · exact (by decide : (2 : ℕ) ≠ 3) (h2.symm.trans hi3)
      · exact (by decide : (2 : ℕ) ≠ 3) (h2.symm.trans hv3)
    rw [hnone, Finset.card_empty, Nat.add_zero] at hdegree
    exact ((SimpleGraph.Iso.comap label (compressed G L)).degree_eq i).symm.trans hdegree
  · intro x y z
    exact compressed_triangle_free hpart hg (label x) (label y) (label z)
  · intro x y
    change (label x ≠ label y ∧ _) ↔ x ≠ y ∧ _
    rw [label.injective.ne_iff]
    rfl

#print axioms compressed_cubic

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoThinSlice
