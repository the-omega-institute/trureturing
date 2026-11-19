import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GraySamePartition

/-! Bound a candidate containing any of the twenty normalized Gray pairs. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayRepresentativeBounds

open Finset
open Q9GrayCrossedPlacement (cube)
open Q9GrayEasyPlacements (supports supports_card sdiff_subset_residual)
open Q9GrayRelativeCenters (representativeCenters)
open Q9GrayPlacementNormalForm (normalize normalize_hammingDist origin)

private def swapBlocks (v : BitVec 9) : BitVec 9 :=
  (v &&& 7) ||| ((v &&& 56) <<< 3) ||| ((v >>> 3) &&& 56)

private theorem swap_involutive : Function.Involutive swapBlocks := by
  change ∀ v : BitVec 9, swapBlocks (swapBlocks v) = v
  decide +kernel

private def swapEquiv : BitVec 9 ≃ BitVec 9 :=
  ⟨swapBlocks, swapBlocks, swap_involutive, swap_involutive⟩

private def swapCoordinates : Equiv.Perm (Fin 9) :=
  (Equiv.swap 3 6).trans ((Equiv.swap 4 7).trans (Equiv.swap 5 8))

private theorem swap_coding : ∀ (v : BitVec 9) (i : Fin 9),
    cubeBitVec 9 (swapBlocks v) i = normalize swapCoordinates origin (cubeBitVec 9 v) i := by
  decide +kernel

private theorem swap_adj (x y : BitVec 9) :
    cube.Adj (swapEquiv x) (swapEquiv y) ↔ cube.Adj x y := by
  have h (v : BitVec 9) := funext (swap_coding v)
  change hammingDist (cubeBitVec 9 (swapBlocks x)) (cubeBitVec 9 (swapBlocks y)) = 1 ↔
    hammingDist (cubeBitVec 9 x) (cubeBitVec 9 y) = 1
  rw [h x, h y, normalize_hammingDist]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Verify the coordinate swap against the already proved crossed placement.
private theorem swap_supports :
    (supports 1 504).map swapEquiv.toEmbedding = Q9GrayCrossedPlacement.supportUnion := by
  decide +kernel

private theorem crossed_bound
    (U : Finset (BitVec 9)) (hU : supports 1 504 ⊆ U)
    (hclosed : ∀ x ∈ supports 1 504, ∀ y ∈ U, cube.Adj x y → y ∈ supports 1 504)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 254 := by
  let W := U.map swapEquiv.toEmbedding
  have hsup : Q9GrayCrossedPlacement.supportUnion ⊆ W := by
    rw [← swap_supports]
    exact map_subset_map.mpr hU
  have hcl : ∀ x ∈ Q9GrayCrossedPlacement.supportUnion, ∀ y ∈ W,
      cube.Adj x y → y ∈ Q9GrayCrossedPlacement.supportUnion := by
    intro x hx y hy ha
    rw [← swap_supports] at hx ⊢
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_map.mp hy
    exact mem_map.mpr ⟨y', hclosed x' hx' y' hy' ((swap_adj x' y').mp ha), rfl⟩
  have hW : ∀ v ∈ W, (W.filter (cube.Adj v)).card ≤ 3 := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hv
    unfold W
    rw [filter_map, card_map]
    simpa only [Function.comp_apply, Equiv.toEmbedding_apply, swap_adj] using hdeg x hx
  have h := Q9GrayCrossedPlacement.candidate_card_le W hsup hcl hW
  simpa only [W, card_map] using h

/-- In every normalized placement, a degree-three candidate whose two
supports are a union of components has at most 257 vertices. -/
theorem candidate_card_le (k : Fin 5) (t : BitVec 9)
    (ht : t ∈ representativeCenters k) (U : Finset (BitVec 9))
    (hU : supports k t ⊆ U)
    (hclosed : ∀ x ∈ supports k t, ∀ y ∈ U, cube.Adj x y → y ∈ supports k t)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 257 := by
  by_cases h0 : k = 0 ∧ t = 63
  · obtain ⟨rfl, rfl⟩ := h0
    have h := Q9GraySamePartition.residual_card_le (U \ supports 0 63)
      (sdiff_subset_residual 0 63 U hclosed) (fun v hv =>
        (card_le_card (filter_subset_filter _ sdiff_subset)).trans (hdeg v (mem_sdiff.mp hv).1))
    rw [card_sdiff_of_subset hU, supports_card _ _ ht] at h
    omega
  by_cases h1 : k = 1 ∧ t = 504
  · obtain ⟨rfl, rfl⟩ := h1
    exact (crossed_bound U hU hclosed hdeg).trans (by omega)
  · exact Q9GrayEasyPlacements.candidate_card_le k t ht h0 h1 U hU hclosed hdeg

#print axioms candidate_card_le

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayRepresentativeBounds
