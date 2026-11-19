import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric

/-! The parity splits of a twenty-two-vertex half after suppressing its cut endpoints. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression

open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
open GirthSliceCounting (degreeTwo degreeThree)
open private paritySide parity_bipartite parity_union parts_card sum_degrees_parts
  coordinate_slice_degree_cases coordinate_slice_low_independent low_slice_card_eq_q
  balanced_subset from D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private SideHigh compressed compressed_triangle_free from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private compressed_edge_count from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSymmetric

attribute [local instance] Classical.propDecidable

private theorem three_vertices_not_three_edges {V : Type*} [Fintype V]
    (H : SimpleGraph V) (hV : Fintype.card V = 3)
    (htriangle : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) :
    H.edgeFinset.card ≠ 3 := by
  intro hE
  have hsum := H.sum_degrees_eq_twice_card_edges
  rw [hE] at hsum
  have hcap (x : V) : H.degree x ≤ 2 := by
    have h := H.degree_lt_card_verts x
    omega
  have hreg (x : V) : H.degree x = 2 := by
    by_contra hx
    have hlt : H.degree x < 2 := by have h := hcap x; omega
    have h := Finset.sum_lt_sum (s := (univ : Finset V))
      (fun y _ => hcap y) ⟨x, mem_univ _, hlt⟩
    simp only [Finset.sum_const, Finset.card_univ, hV, smul_eq_mul] at h
    omega
  have hall (x y : V) (hxy : x ≠ y) : H.Adj x y := by
    apply (H.degree_eq_card_sub_one x).mp
    · rw [hV, hreg]
    · exact hxy
  let e := (Fintype.equivFinOfCardEq hV).symm
  exact htriangle (e 0) (e 1) (e 2)
    (hall _ _ (e.injective.ne (by decide))) (hall _ _ (e.injective.ne (by decide)))
    (hall _ _ (e.injective.ne (by decide)))

private theorem five_vertices_six_edges {V : Type*} [Fintype V]
    (H : SimpleGraph V) (hV : Fintype.card V = 5)
    (hE : H.edgeFinset.card = 6)
    (htriangle : ∀ x y z, H.Adj x y → H.Adj y z → H.Adj z x → False) :
    Nonempty (H ≃g turanGraph 5 2) := by
  have hfree : H.CliqueFree 3 := by
    rw [cliqueFree_iff_isEmpty_copy_top_fin]
    constructor
    intro f
    exact htriangle (f 0) (f 1) (f 2)
      (f.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1))
      (f.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 1 2))
      (f.toHom.map_adj (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 2 0))
  have hm : H.IsTuranMaximal 2 := by
    refine ⟨hfree, ?_⟩
    intro K _ hk
    have hle := hk.card_edgeFinset_le
    simpa [hV, hE, turanNumber_two] using hle
  exact hV ▸ hm.nonempty_iso_turanGraph

/-- A 22-vertex coordinate half compresses to parity classes of orders 1 and 9,
or to two copies of the complete bipartite graph on parts of orders 2 and 3. -/
theorem half_compression {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 22) :
    ∃ p : Bool,
      let S := coordinateSlice C b
      let G := (hypercube 9).induce (S : Set (Q 9))
      let L := paritySide S p
      let R := paritySide S (!p)
      (Fintype.card (SideHigh G L) = 1 ∧ Fintype.card (SideHigh G R) = 9 ∧
        (compressed G L).edgeFinset.card = 0 ∧ (compressed G R).edgeFinset.card = 12) ∨
      (Nonempty (compressed G L ≃g turanGraph 5 2) ∧
        Nonempty (compressed G R ≃g turanGraph 5 2)) := by
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  let L := paritySide S false
  let R := paritySide S true
  have hdeg (v : (S : Set (Q 9))) : G.degree v = 2 ∨ G.degree v = 3 :=
    coordinate_slice_degree_cases v.property hr
  have hlow {v w : (S : Set (Q 9))} (hvw : G.Adj v w)
      (hv : G.degree v = 2) (hw : G.degree w = 2) : False :=
    coordinate_slice_low_independent hr hb hvw hv hw
  have hcut : 6 * directionEdges C 0 = C.card := by
    simpa using direction_edge_count (d := 3) C hr hb 0
  have hcount : (degreeTwo G univ).card = 12 := by
    rw [low_slice_card_eq_q hr]
    omega
  have hp : G.IsBipartiteWith (L : Set _) (R : Set _) := parity_bipartite S
  have hd : Disjoint L R := by simpa only [Finset.disjoint_coe] using hp.disjoint
  have hu : L ∪ R = univ := parity_union S
  have hab : L.card + R.card = 22 := by
    rw [← card_union_of_disjoint hd, hu, card_univ]
    simpa using hs
  have hd₂ : Disjoint (degreeTwo G L) (degreeTwo G R) :=
    hd.mono (filter_subset _ _) (filter_subset _ _)
  have hu₂ : degreeTwo G L ∪ degreeTwo G R = degreeTwo G univ := by
    simp only [degreeTwo, ← filter_union, hu]
  have hlows : (degreeTwo G L).card + (degreeTwo G R).card = 12 := by
    rw [← card_union_of_disjoint hd₂, hu₂, hcount]
  have hsum : 2 * (degreeTwo G L).card + 3 * (degreeThree G L).card =
      2 * (degreeTwo G R).card + 3 * (degreeThree G R).card :=
    (sum_degrees_parts G hdeg L).symm.trans
      ((SimpleGraph.isBipartiteWith_sum_degrees_eq hp).trans (sum_degrees_parts G hdeg R))
  have hL := parts_card G hdeg L
  have hR := parts_card G hdeg R
  have hg := BalancedCubeGirth.eight_le_egirth S (balanced_subset hb (filter_subset _ _))
  have heL := compressed_edge_count hp hdeg (fun hxy hx hy => hlow hxy hx hy) hg
  have heR := compressed_edge_count hp.symm hdeg (fun hxy hx hy => hlow hxy hx hy) hg
  have hcard (T : Finset (S : Set (Q 9))) :
      Fintype.card (SideHigh G T) = (degreeThree G T).card := Fintype.card_coe _
  have hnL : (degreeThree G L).card ≠ 3 := by
    intro h
    have ht := compressed_triangle_free hp hg
    exact three_vertices_not_three_edges _ ((hcard L).trans h) ht (by omega)
  have hnR : (degreeThree G R).card ≠ 3 := by
    intro h
    have ht := compressed_triangle_free hp.symm hg
    exact three_vertices_not_three_edges _ ((hcard R).trans h) ht (by omega)
  have hsplit : (degreeThree G L).card = 1 ∨ (degreeThree G L).card = 5 ∨
      (degreeThree G R).card = 1 := by omega
  rcases hsplit with h | h | h
  · exact ⟨false, Or.inl ⟨(hcard L).trans h, (hcard R).trans (by omega),
      heL.trans (by omega), heR.trans (by omega)⟩⟩
  · exact ⟨false, Or.inr
      ⟨five_vertices_six_edges _ ((hcard L).trans h) (heL.trans (by omega))
          (compressed_triangle_free hp hg),
        five_vertices_six_edges _ ((hcard R).trans (by omega)) (heR.trans (by omega))
          (compressed_triangle_free hp.symm hg)⟩⟩
  · exact ⟨true, Or.inl ⟨(hcard R).trans h, (hcard L).trans (by omega),
      heR.trans (by omega), heL.trans (by omega)⟩⟩

#print axioms half_compression

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoCompression
