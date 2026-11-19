import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch

/-! Verify the opposite-half exclusions for the normalized twenty-two-point
masks. Coverage by the mask list is an independent geometric claim. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoUnsignedCertificate

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip_flip)
open BalancedCubeLowerBound (coordinateSlice)
open HuangCutParity (halfParity mem_flip_iff_halfParity)
open private indicator from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangCutParity
open private adjacent adjacent_iff toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
open private coordinate_slice_card_sum coordinate_slices_partition from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation

local notation "flip" => BalancedCriticalSpectrum.flip
private abbrev Vertex := BitVec 9

private instance : Fintype Vertex :=
  Fintype.ofEquiv (Fin (2 ^ 9)) (BitVec.equivFin (m := 9)).toEquiv.symm

/-- Occupancy masks arising in the finite normalized geometry search. -/
def masks : List Nat := [
  0x40040045500551014404140115,
  0x40040045501000514454140115,
  0x40040045501550014404140115,
  0x40100051440400455054140115,
  0x400004045500551041401440115,
  0x400004045501000541451440115,
  0x400004045501550041401440115,
  0x551040004140040014445500115,
  0x1000004051440400541445500115,
  0x1000040054140040514445500115,
  0x1550040004140040014445500115,
  0x40000045500040004445500115 |||
    (0x4000000000004000404 <<< 128),
  0x11500000115000001100115 |||
    (0x400000004000000040004 <<< 128) |||
    (0x400000004000000040004 <<< 256),
]

private def marked (mask : Nat) (x : Vertex) : ZMod 2 :=
  if mask.testBit x.toNat then 1 else 0

private def parity (mask : Nat) (x : Vertex) : ZMod 2 :=
  marked mask x + ∑ i ∈ Finset.univ.erase (0 : Fin 9), marked mask (toggle x i)

private def firstHalf (mask : Nat) : Finset Vertex :=
  Finset.univ.filter fun x => mask.testBit x.toNat = true

private def oppositeHalf (mask : Nat) : Finset Vertex :=
  Finset.univ.filter fun y => y.getLsbD 0 = true ∧ parity mask (toggle y 0) = 1

private def bad (mask : Nat) : Bool :=
  let R := oppositeHalf mask
  let U := firstHalf mask ∪ R
  decide (R.card ≠ 50) ||
    decide ((149 : Vertex) ∈ R ∧ 3 < (U.filter (fun y => adjacent 149 y = true)).card)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Check all masks, including the size-50 reconstruction with a degree-five vertex.
private theorem checked : masks.all bad = true := by
  decide +kernel

attribute [local instance] Classical.propDecidable

private theorem parity_eq {mask : Nat} {S : Finset (Q 9)}
    (hm : ∀ x : Vertex, mask.testBit x.toNat = true ↔ cubeBitVec 9 x ∈ S) (x : Vertex) :
    parity mask x = halfParity S (cubeBitVec 9 x) := by
  have hterm (v : Vertex) : marked mask v = indicator S (cubeBitVec 9 v) := by
    by_cases h : mask.testBit v.toNat = true
    · simp [marked, indicator, h, (hm v).mp h]
    · simp [marked, indicator, h, mt (hm v).mpr h]
  rw [parity, halfParity, hterm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hterm]
  congr 1
  exact cubeBitVec_xor_single x i

set_option maxRecDepth 8192 in
/-- A 22-vertex half represented by a listed mask cannot extend to a balanced
cubic support of order 72. -/
theorem no_extension_of_listed_half {C : Finset (Q 9)} {mask : Nat}
    (hc : C.card = 72) (hs : (coordinateSlice C false).card = 22)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hlist : mask ∈ masks)
    (hm : ∀ x : Vertex, mask.testBit x.toNat = true ↔ cubeBitVec 9 x ∈ coordinateSlice C false) :
    False := by
  classical
  let e := cubeBitVec 9
  have hR : oppositeHalf mask = (coordinateSlice C true).map e.symm.toEmbedding := by
    ext y
    have hy : y ∈ (coordinateSlice C true).map e.symm.toEmbedding ↔ e y ∈ coordinateSlice C true := by
      constructor
      · rintro h
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp h
        simpa using hx
      · intro h
        exact Finset.mem_map.mpr ⟨e y, h, e.symm_apply_apply y⟩
    rw [hy]
    by_cases h : y.getLsbD 0 = true
    · have hcut : (e (toggle y 0)) 0 = false := by
        rw [show e (toggle y 0) = flip (e y) 0 from cubeBitVec_xor_single y 0]
        have hh : e y 0 = true := h
        simp [hh]
      have hp := mem_flip_iff_halfParity hr hb hcut
      rw [← parity_eq hm, show e (toggle y 0) = flip (e y) 0 from cubeBitVec_xor_single y 0,
        BalancedCriticalSpectrum.flip_flip] at hp
      have hh : e y 0 = true := h
      simpa only [oppositeHalf, coordinateSlice, Finset.mem_filter, Finset.mem_univ,
        true_and, and_true, h, hh] using hp.symm
    · constructor
      · intro hmR
        exact (h (Finset.mem_filter.mp hmR).2.1).elim
      · intro hmC
        exact (h (Finset.mem_filter.mp hmC).2).elim
  have hL : firstHalf mask = (coordinateSlice C false).map e.symm.toEmbedding := by
    ext y
    simp only [firstHalf, Finset.mem_filter, Finset.mem_univ, true_and, hm]
    constructor
    · intro h
      exact Finset.mem_map.mpr ⟨e y, h, e.symm_apply_apply y⟩
    · intro h
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp h
      change e (e.symm x) ∈ coordinateSlice C false
      simpa only [e.apply_symm_apply] using hx
  have hU : firstHalf mask ∪ oppositeHalf mask = C.map e.symm.toEmbedding := by
    rw [hL, hR, ← Finset.map_union, coordinate_slices_partition]
  have hsize : (oppositeHalf mask).card = 50 := by
    rw [hR, Finset.card_map]
    have h := coordinate_slice_card_sum C
    omega
  have hbad := List.all_eq_true.mp checked mask hlist
  have hw : (149 : Vertex) ∈ oppositeHalf mask ∧
      3 < ((firstHalf mask ∪ oppositeHalf mask).filter (fun z => adjacent 149 z = true)).card := by
    unfold bad at hbad
    have hh := (Bool.or_eq_true_iff.mp hbad).resolve_left (by simp [hsize])
    exact of_decide_eq_true hh
  have hmem : e (149 : Vertex) ∈ C := by
    have hm' := Finset.mem_union_right (firstHalf mask) hw.1
    rw [hU] at hm'
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hm'
    have he : e.symm x = (149 : Vertex) := hxy
    rwa [← he, e.apply_symm_apply]
  have hf : ((C.map e.symm.toEmbedding).filter (fun w => adjacent 149 w = true)).card =
      ((hypercube 9).neighborFinset (e 149) ∩ C).card := by
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter, Function.comp_apply, Equiv.toEmbedding_apply,
      adjacent_iff, SimpleGraph.mem_neighborFinset, and_comm]
    change (_ ∧ (hypercube 9).Adj (e 149) (e (e.symm v))) ↔ _
    rw [e.apply_symm_apply]
  have hdegree := hw.2
  rw [hU, hf, selected_neighbor_card hmem, hr.degree_eq] at hdegree
  omega

#print axioms no_extension_of_listed_half

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoUnsignedCertificate
