import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9WeightedEdgeBound
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoExtension
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinEdgeData
import Batteries.Tactic.OpenPrivate

/-! Cardinality bounds for the seven representatives of thin Q9 components. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinEdgeCertificates

open Finset
open Q9GrayCrossedPlacement (cube)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open private adjacent adjacent_iff toggle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private fastCube from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoExtension

private abbrev Vertex := BitVec 9

private instance : Fintype Vertex :=
  Fintype.ofEquiv (Fin (2 ^ 9)) (BitVec.equivFin (m := 9)).toEquiv.symm

private instance : DecidableRel fastCube.Adj := fun x y =>
  inferInstanceAs (Decidable (adjacent x y = true))

private theorem toggle_injective (x : Vertex) : Function.Injective (toggle x) := by
  intro i j h
  have powers : ∀ (a b : Fin 9),
      BitVec.ofNat 9 (2 ^ a.val) = BitVec.ofNat 9 (2 ^ b.val) → a = b := by
    decide +kernel
  exact powers i j ((BitVec.xor_right_inj x).mp h)

private theorem toggle_adj (x : Vertex) (i : Fin 9) : fastCube.Adj x (toggle x i) := by
  apply (adjacent_iff _ _).mpr
  rw [toggle, cubeBitVec_xor_single]
  exact BalancedCriticalSpectrum.flip_adj _ _

private theorem exists_toggle {x y : Vertex} (h : fastCube.Adj x y) :
    ∃ i, toggle x i = y := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip ((adjacent_iff _ _).mp h)
  refine ⟨i, (cubeBitVec 9).injective ?_⟩
  rw [toggle, cubeBitVec_xor_single, hi]
  rfl

private theorem sum_directions (R : Finset Vertex) (x : Vertex) (f : Vertex → ℤ)
    (hzero : ∀ y ∈ R, ¬fastCube.Adj x y → f y = 0) :
    (∑ y ∈ R, f y) = ∑ i ∈ univ.filter (fun i => toggle x i ∈ R), f (toggle x i) := by
  let e : Fin 9 ↪ Vertex := ⟨toggle x, toggle_injective x⟩
  have hmap : (univ.filter (fun i => toggle x i ∈ R)).map e = R.filter (fastCube.Adj x) := by
    ext y
    rw [mem_map, mem_filter]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(mem_filter.mp hi).2, toggle_adj x i⟩
    · rintro ⟨hy, ha⟩
      obtain ⟨i, hi⟩ := exists_toggle ha
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi.symm ▸ hy⟩, hi⟩
  have hr : (∑ y ∈ R.filter (fastCube.Adj x), f y) = ∑ y ∈ R, f y := by
    rw [sum_filter]
    apply sum_congr rfl
    intro y hy
    by_cases h : fastCube.Adj x y
    · simp [h]
    · simp [h, hzero y hy h]
  rw [← hr, ← hmap, sum_map]
  rfl

private def inSupport (k : Fin 7) (v : Vertex) : Bool :=
  (supportMask k).testBit v.toNat

/-- The seven representatives, as sets of cube vertices. -/
def support (k : Fin 7) : Finset Vertex :=
  univ.filter fun v => inSupport k v

private def inResidual (k : Fin 7) (v : Vertex) : Bool :=
  (residualMask k).testBit v.toNat

private def region (k : Fin 7) : Finset Vertex :=
  univ.filter fun v => inResidual k v

private def vertexWeight (k : Fin 7) (x : Vertex) : ℤ := weight k x.toNat 0
private def slackWeight (k : Fin 7) (x : Vertex) : ℤ := weight k x.toNat 1

private def edgeWeight (k : Fin 7) (x y : Vertex) : ℤ :=
  if adjacent x y then weight k x.toNat (2 + Nat.log2 ((x ^^^ y).toNat)) else 0

private def axisWeight (k : Fin 7) (x : Vertex) (i : Fin 9) : ℤ :=
  weight k x.toNat (2 + i.val)

private theorem edge_toggle (k : Fin 7) (x : Vertex) (i : Fin 9) :
    edgeWeight k x (toggle x i) = axisWeight k x i := by
  have ha : adjacent x (toggle x i) = true := toggle_adj x i
  have hpow : ∀ j : Fin 9, (BitVec.ofNat 9 (2 ^ j.val)).toNat.log2 = j.val := by
    decide +kernel
  simp only [edgeWeight, axisWeight, ha, ↓reduceIte]
  rw [toggle, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, hpow]

private theorem toggle_twice (x : Vertex) (i : Fin 9) : toggle (toggle x i) i = x := by
  simp only [toggle, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

private def around (k : Fin 7) (x : Vertex) : ℤ :=
  ∑ i ∈ univ.filter (fun i => inResidual k (toggle x i)), axisWeight k x i

private theorem edge_zero (k : Fin 7) (x y : Vertex) (h : ¬fastCube.Adj x y) :
    edgeWeight k x y = 0 := by
  cases ha : adjacent x y
  · simp [edgeWeight, ha]
  · exact (h ha).elim

private theorem edge_nonneg (k : Fin 7) (x y : Vertex) : 0 ≤ edgeWeight k x y := by
  unfold edgeWeight
  split <;> positivity

private theorem around_eq (k : Fin 7) (x : Vertex) :
    (∑ y ∈ region k, edgeWeight k x y) = around k x := by
  rw [sum_directions (region k) x (edgeWeight k x) (fun y _ => edge_zero k x y)]
  apply sum_congr
  · ext i
    simp [region]
  · intro i _
    exact edge_toggle k x i

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- Replay the scaled weight inequalities at each residual vertex and edge.
private theorem verified (k : Fin 7) :
    (support k).card = 72 ∧
    (∀ v : Vertex, inSupport k v = false → (∀ i : Fin 9, inSupport k (toggle v i) = false) →
      inResidual k v = true) ∧
    (∀ x : Vertex, inResidual k x = true →
      1000000 + 3 * vertexWeight k x ≤ around k x + slackWeight k x) ∧
    (∀ (x : Vertex) (i : Fin 9), inResidual k x = true → inResidual k (toggle x i) = true →
      axisWeight k x i = axisWeight k (toggle x i) i ∧
      axisWeight k x i ≤ vertexWeight k x + vertexWeight k (toggle x i)) ∧
    ((∑ x ∈ region k, around k x) + 2 * ∑ x ∈ region k, slackWeight k x) < 372000000 := by
  fin_cases k <;> decide +kernel

private theorem card_residual_lt (k : Fin 7) (S : Finset Vertex) (hS : S ⊆ region k)
    (hdeg : ∀ v ∈ S, (S.filter (fastCube.Adj v)).card ≤ 3) : S.card < 186 := by
  obtain ⟨_, _, hcover, hedges, hmass⟩ := verified k
  have hflag {v : Vertex} (hv : v ∈ region k) : inResidual k v = true :=
    (mem_filter.mp hv).2
  have hsym (x : Vertex) (hx : x ∈ region k) (y : Vertex) (hy : y ∈ region k) :
      edgeWeight k x y = edgeWeight k y x := by
    by_cases ha : fastCube.Adj x y
    · obtain ⟨i, rfl⟩ := exists_toggle ha
      have hz := (hedges x i (hflag hx) (hflag hy)).1
      rw [edge_toggle]
      have hreverse : edgeWeight k (toggle x i) x = axisWeight k (toggle x i) i := by
        simpa only [toggle_twice] using edge_toggle k (toggle x i) i
      rw [hreverse]
      exact hz
    · rw [edge_zero k x y ha, edge_zero k y x (fun h => ha h.symm)]
  have hcapacity (x : Vertex) (hx : x ∈ region k) (y : Vertex) (hy : y ∈ region k)
      (ha : fastCube.Adj x y) : edgeWeight k x y ≤ vertexWeight k x + vertexWeight k y := by
    obtain ⟨i, rfl⟩ := exists_toggle ha
    rw [edge_toggle]
    exact (hedges x i (hflag hx) (hflag hy)).2
  have h := Q9WeightedEdgeBound.card_le_of_weights fastCube (region k) S hS 3 hdeg
    (vertexWeight k) (slackWeight k) (edgeWeight k) 1000000
    (fun _ _ => Int.natCast_nonneg _) (fun _ _ => Int.natCast_nonneg _)
    (fun x _ y _ => edge_nonneg k x y) hsym
    (fun x _ y _ => edge_zero k x y) hcapacity
    (fun x hx => by rw [around_eq]; exact hcover x (hflag hx))
  simp only [around_eq] at h
  have hlt := h.trans_lt hmass
  exact_mod_cast (show (S.card : ℤ) < 186 by omega)

/-- Every induced degree-three graph containing any representative as a
component has at most 257 vertices. -/
theorem card_le_of_representative (k : Fin 7) (U : Finset Vertex) (hU : support k ⊆ U)
    (hclosed : ∀ x ∈ support k, ∀ y ∈ U, cube.Adj x y → y ∈ support k)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 257 := by
  have hsub : U \ support k ⊆ region k := by
    intro x hx
    obtain ⟨hxU, hxS⟩ := mem_sdiff.mp hx
    have hz (v : Vertex) (hv : v ∉ support k) : inSupport k v = false := by
      cases hb : inSupport k v
      · rfl
      · exact (hv (mem_filter.mpr ⟨mem_univ _, hb⟩)).elim
    refine mem_filter.mpr ⟨mem_univ _, (verified k).2.1 x (hz _ hxS) ?_⟩
    intro i
    apply hz
    intro hi
    exact hxS (hclosed _ hi _ hxU ((adjacent_iff _ _).mp (toggle_adj x i)).symm)
  have hdeg' : ∀ v ∈ U \ support k, ((U \ support k).filter (fastCube.Adj v)).card ≤ 3 := by
    intro v hv
    have hg : (U \ support k).filter (fastCube.Adj v) ⊆ U.filter (cube.Adj v) := by
      intro x hx
      obtain ⟨hx, ha⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨(mem_sdiff.mp hx).1, (adjacent_iff v x).mp ha⟩
    exact (card_le_card hg).trans (hdeg v (mem_sdiff.mp hv).1)
  have h := card_residual_lt k (U \ support k) hsub hdeg'
  rw [card_sdiff_of_subset hU, (verified k).1] at h
  have hsize := card_le_card hU
  rw [(verified k).1] at hsize
  omega

#print axioms card_le_of_representative

/-- The same upper bound applies to each coordinate isometric copy of
any covered representative. -/
theorem card_le_of_representative_image (k : Fin 7) (U C : Finset Vertex)
    (e : Vertex ≃ Vertex) (he : ∀ x y, cube.Adj (e x) (e y) ↔ cube.Adj x y)
    (hmodel : C.map e.toEmbedding = support k) (hU : C ⊆ U)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, cube.Adj x y → y ∈ C)
    (hdeg : ∀ v ∈ U, (U.filter (cube.Adj v)).card ≤ 3) : U.card ≤ 257 := by
  let W := U.map e.toEmbedding
  have hs : support k ⊆ W := hmodel ▸ map_subset_map.mpr hU
  have hcl : ∀ x ∈ support k, ∀ y ∈ W, cube.Adj x y → y ∈ support k := by
    intro x hx y hy ha
    rw [← hmodel] at hx ⊢
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hy
    exact mem_map.mpr ⟨v, hclosed u hu v hv ((he u v).mp ha), rfl⟩
  have hd : ∀ v ∈ W, (W.filter (cube.Adj v)).card ≤ 3 := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hv
    unfold W
    rw [filter_map, card_map]
    simpa only [Function.comp_apply, Equiv.toEmbedding_apply, he] using hdeg x hx
  simpa only [W, card_map] using card_le_of_representative k W hs hcl hd

#print axioms card_le_of_representative_image

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9ThinEdgeCertificates
