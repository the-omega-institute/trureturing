import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayCrossedPlacement
import D5.S3.Combinatorics.Graph.HypercubeCritical.GrayOmissionCounting
import Batteries.Tactic.OpenPrivate

/-! A degree-row bound for extending a normalized 72-vertex support. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoExtension

open Finset
open Q9GrayCrossedPlacement (cube)
open GrayOmissionCounting (Row demand coefficient Valid weighted_omissions)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open private adjacent adjacent_iff toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch

private abbrev Vertex := BitVec 9

private instance : Fintype Vertex :=
  Fintype.ofEquiv (Fin (2 ^ 9)) (BitVec.equivFin (m := 9)).toEquiv.symm

private def fastCube : SimpleGraph Vertex where
  Adj x y := adjacent x y = true
  symm := ⟨fun _ _ h => (adjacent_iff _ _).mpr ((adjacent_iff _ _).mp h).symm⟩
  loopless := ⟨fun _ h => cube.irrefl ((adjacent_iff _ _).mp h)⟩

private instance : DecidableRel fastCube.Adj := fun x y =>
  inferInstanceAs (Decidable (adjacent x y = true))

private def masked (mask : Nat) : Finset Vertex :=
  univ.filter fun x => mask.testBit x.toNat = true

/-- A normalized 72-vertex support whose compressed half uses the three
disjoint root-axis pairs `{1,4}`, `{2,5}` and `{3,6}`. -/
def support : Finset Vertex :=
  masked ((0x8000a2208a08020080a800200008022a <<< 256) |||
    0x8000a2208a08020080a800200008022a4000d330c70c0100c07c00100004033d)

private def residual : Finset Vertex :=
  univ.filter fun x => x ∉ support ∧ ∀ i : Fin 9, toggle x i ∉ support

private def region : Finset Vertex :=
  masked ((0x7fff5ddf75f7fdff7f57ffdffff7fdd51557044d107154d517015d457551d440 <<< 256) |||
    0x1557044d107154d517015d457551d4402883000c003028c203002c823882c000)

private def weight (x : Vertex) : ℕ :=
  if (((0x2880411041042802401420820882011414400000000014010000104104410000 <<< 256) |||
    0x1440000000001401000010410441000000000000000000000000000000000000) : Nat).testBit x.toNat
  then 9
  else if (((0x3000c003000c003000c003000c00000010004001000400100040010004000 <<< 256) |||
    0x1000400100040010004001000400000000000000000000000000000000000) : Nat).testBit x.toNat then 3
  else if (((0x228088220828028280282088220288001140441104140141401410441101440 <<< 256) |||
    0x114044110414014140141044110144000000000000000000000000000000000) : Nat).testBit x.toNat then 1
  else 0

set_option maxRecDepth 4096 in
private theorem region_eq_residual : region = residual := by decide +kernel

private def row (x : (region : Set Vertex)) : Row Vertex := .degree x.val

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
-- Check every vertex load and the total demand of the integer certificate.
private theorem checked :
    support.card = 72 ∧ region.card = 240 ∧
    (∀ x ∈ region, (∑ i, weight i.val * coefficient fastCube region (row i) x) ≤ 27) ∧
    (∑ i, weight i.val * demand fastCube region (row i)) = 1692 := by
  decide +kernel

/-- The explicit 72-vertex component can occur in a degree-three restriction
of the nine-cube only if that restriction has at most 249 vertices. -/
theorem card_le_of_closed_support (U : Finset Vertex) (hU : support ⊆ U)
    (hclosed : ∀ x ∈ support, ∀ y ∈ U, cube.Adj x y → y ∈ support)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 249 := by
  have hsub : U \ support ⊆ region := by
    rw [region_eq_residual]
    intro x hx
    obtain ⟨hxU, hxS⟩ := mem_sdiff.mp hx
    refine mem_filter.mpr ⟨mem_univ _, hxS, fun i hi => hxS (hclosed _ hi _ hxU ?_)⟩
    apply SimpleGraph.Adj.symm
    change (hypercube 9).Adj (cubeBitVec 9 x) (cubeBitVec 9 (toggle x i))
    rw [toggle, cubeBitVec_xor_single]
    exact BalancedCriticalSpectrum.flip_adj _ _
  have hdeg' : ∀ v ∈ U \ support, ((U \ support).filter (fastCube.Adj v)).card ≤ 3 := by
    intro v hv
    have hsub' : (U \ support).filter (fastCube.Adj v) ⊆ U.filter (cube.Adj v) := by
      intro x hx
      obtain ⟨hx, ha⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_sdiff.mp hx).1, (adjacent_iff v x).mp ha⟩
    exact (card_le_card hsub').trans (hdeg v (mem_sdiff.mp hv).1)
  obtain ⟨hsupport, hregion, hload, hbound⟩ := checked
  have h := weighted_omissions fastCube region (U \ support) hsub hdeg' row
    (fun i => weight i.val) 27 (fun i => i.property) hload
  rw [hbound, hregion, card_sdiff_of_subset hU, hsupport] at h
  have hcard := card_le_card hU
  omega

#print axioms card_le_of_closed_support

/-- The same upper bound holds throughout the cube automorphism orbit
of the explicit support. -/
theorem card_le_of_closed_support_image (U C : Finset Vertex) (e : Vertex ≃ Vertex)
    (he : ∀ x y, cube.Adj (e x) (e y) ↔ cube.Adj x y)
    (hmodel : C.map e.toEmbedding = support) (hU : C ⊆ U)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, cube.Adj x y → y ∈ C)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 249 := by
  let V := U.map e.toEmbedding
  have hsup : support ⊆ V := by
    rw [← hmodel]
    exact map_subset_map.mpr hU
  have hcl : ∀ x ∈ support, ∀ y ∈ V, cube.Adj x y → y ∈ support := by
    intro x hx y hy ha
    rw [← hmodel] at hx ⊢
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
    exact mem_map.mpr ⟨v, hclosed u hu v hv ((he u v).mp ha), rfl⟩
  have hd : ∀ v ∈ V, (V.filter (cube.Adj v)).card ≤ 3 := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hv
    unfold V
    rw [filter_map, card_map]
    simpa only [Function.comp_apply, Equiv.toEmbedding_apply, he] using hdeg x hx
  simpa only [V, card_map] using card_le_of_closed_support V hsup hcl hd

#print axioms card_le_of_closed_support_image

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoExtension
