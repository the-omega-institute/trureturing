import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedCoverage
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction

/-! Transfer the computed degree obstruction to the actual induced cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedExtension

open scoped Classical
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9TwentyTwoReconstruction (bit_iff_opposite_mem)
open private adjacent_exists_flip flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private flip_direction_injective from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeLayerDisjointness
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
open private toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
open private same_cut from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoReconstruction
open private hasExcessDegree reconstructedMask from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedPlacements

local notation "flip" => BalancedCriticalSpectrum.flip
private abbrev Vertex := BitVec 9

private theorem count_neighbors (C : Finset (Q 9)) (y : Q 9) :
    ((List.finRange 9).countP fun a => decide (flip y a ∈ C)) =
      ((hypercube 9).neighborFinset y ∩ C).card := by
  classical
  let occupied := ((List.finRange 9).filter fun a => decide (flip y a ∈ C)).map (flip y)
  have hnodup : occupied.Nodup :=
    ((List.nodup_finRange 9).filter _).map (fun _ _ h => flip_direction_injective y h)
  have hset : occupied.toFinset = (hypercube 9).neighborFinset y ∩ C := by
    ext z
    simp only [occupied, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_finRange,
      decide_eq_true_eq, true_and, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨BalancedCriticalSpectrum.flip_adj y a, ha⟩
    · rintro ⟨h, hz⟩
      obtain ⟨a, rfl⟩ := adjacent_exists_flip h
      exact ⟨a, hz, rfl⟩
  rw [← hset, List.toFinset_card_of_nodup hnodup, List.countP_eq_length_filter]
  simp [occupied]

/-- A computed excess degree in a parity reconstruction excludes an actual
balanced cubic extension of the same first half. -/
theorem no_extension_of_excess_degree {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (half : List Vertex) (hn : half.Nodup)
    (hm : ∀ x : Vertex, x ∈ half ↔ cubeBitVec 9 x ∈ coordinateSlice C false)
    (bad : hasExcessDegree half = true) : False := by
  classical
  let e := cubeBitVec 9
  unfold hasExcessDegree at bad
  obtain ⟨i, hi, h⟩ := List.any_eq_true.mp bad
  let x := BitVec.ofNat 9 (2 * i)
  let y := flip (e x) 0
  let mask := reconstructedMask half
  change (mask.testBit i && decide (3 < (half.contains x).toNat +
    (List.finRange 8).countP (fun a => mask.testBit ((toggle x a.succ).toNat / 2)))) = true at h
  obtain ⟨hy, excess⟩ := Bool.and_eq_true_iff.mp h
  have hxnat : x.toNat = 2 * i := by
    have hi' := List.mem_range.mp hi
    simp [x]
    omega
  have hcut : x.getLsbD 0 = false := by
    apply Nat.mod_two_eq_zero_iff_testBit_zero.mp
    rw [hxnat]
    omega
  have bit (z : Vertex) (hz : z.getLsbD 0 = false) :
      mask.testBit (z.toNat / 2) = true ↔ flip (e z) 0 ∈ C :=
    bit_iff_opposite_mem hr hb half hn hm hz
  have hymem : y ∈ C := (bit x hcut).mp (by rwa [hxnat, show 2 * i / 2 = i by omega])
  have cross : decide (flip y 0 ∈ C) = half.contains x := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.contains_iff_mem, hm]
    have hx : cubeBitVec 9 x 0 = false := hcut
    simp [e, y, coordinateSlice, hx]
  have within (a : Fin 8) : decide (flip y a.succ ∈ C) =
      mask.testBit ((toggle x a.succ).toNat / 2) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, bit _ (same_cut hcut a)]
    rw [show e (toggle x a.succ) = flip (e x) a.succ from cubeBitVec_xor_single x a.succ]
    exact iff_of_eq (congrArg (fun z : Q 9 => z ∈ C) (flip_comm (e x) 0 a.succ))
  have hcount : ((List.finRange 9).countP fun a => decide (flip y a ∈ C)) =
      (half.contains x).toNat +
        (List.finRange 8).countP (fun a => mask.testBit ((toggle x a.succ).toNat / 2)) := by
    rw [List.finRange_succ, List.countP_cons, List.countP_map, cross]
    have same : ((fun a : Fin 9 => decide (flip y a ∈ C)) ∘ Fin.succ) =
        fun a : Fin 8 => mask.testBit ((toggle x a.succ).toNat / 2) := funext within
    rw [same, Nat.add_comm]
    cases half.contains x <;> rfl
  rw [count_neighbors, selected_neighbor_card hymem, hr.degree_eq] at hcount
  have hexcess := of_decide_eq_true excess
  omega

#print axioms no_extension_of_excess_degree

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TwentyTwoPairedExtension
