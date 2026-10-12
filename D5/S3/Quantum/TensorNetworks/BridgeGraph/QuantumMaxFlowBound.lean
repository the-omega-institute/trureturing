/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/QuantumMaxFlowBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: QuantumMaxFlowBound for width-three bridge flow. -/

/-
proof_shape: QMaxFlow_attained: bind-only; consumer: CastlingDeficit.concise_maximizer
escape_witness: QMaxFlow_attained: none
proof_shape: rank_le_QMaxFlow: bind-only; consumer: QuantumMaxFlowBound.rational_witness_lower_bound
escape_witness: rank_le_QMaxFlow: none
proof_shape: QMaxFlow_le_outer: bind-only; consumer: QuantumMaxFlowBound.QMaxFlow_le_QMinCut
escape_witness: QMaxFlow_le_outer: none
proof_shape: QMaxFlow_le_QMinCut: bind-only; consumer: QuantumMaxFlowMinCut.result
escape_witness: QMaxFlow_le_QMinCut: none
proof_shape: cone_bounds: bind-only; consumer: QuantumMaxFlowBound.cone_QMinCut
escape_witness: cone_bounds: none
proof_shape: cone_QMinCut: bind-only; consumer: QuantumMaxFlowMinCut.result
escape_witness: cone_QMinCut: none
proof_shape: rationalWitness_full_rank: bind-only; consumer: QuantumMaxFlowMinCut.claim_of_hypotheses
escape_witness: rationalWitness_full_rank: none
proof_shape: typed_three_slice_flow: bind-only; consumer: ShiftPencilBlocks.typed_two_slice_flow
escape_witness: typed_three_slice_flow: none
proof_shape: witness_swap: bind-only; consumer: ShiftPencilBlocks.different_depth_witness
escape_witness: witness_swap: none
proof_shape: widthTwo_proved: content
escape_witness: widthTwo_proved: QuantumMaxFlowBound.mixed_left
admission_basis: escape-witness (widthTwo_proved)
Module content mechanism: mixed_left: an explicit mixed-width identity submatrix construction.
Direct frozen dependencies: none on the implementation baseline.
Utility: none; symbolic constructions and proofs for arbitrary dimensions,
not bounded enumeration, a checker, numeric reduction, or a certified instance.
Information-escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14762
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.Algebra.Algebra.Rat

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Matrix Module

open Matrix Module
section

def flow {K : Type*} [CommSemiring K] {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    Matrix (Fin a × Fin d) (Fin b × Fin c) K :=
  ∑ r : Fin 3, Matrix.kronecker (M r) (N r)

def attainable (a b c d : ℕ) : Set ℕ :=
  {r | ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
          (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ), (flow M N).rank = r}

noncomputable def QMaxFlow (a b c d : ℕ) : ℕ := sSup (attainable a b c d)

def QMinCut (a b c d : ℕ) : ℕ := min (3 * a * c) (min (a * d) (b * c))

private theorem flow_rank_le_outer {K : Type*} [Field K] {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    (flow M N).rank ≤ min (a * d) (b * c) := by
  exact le_min (by simpa using (flow M N).rank_le_card_height)
    (by simpa using (flow M N).rank_le_card_width)

private theorem attainable_nonempty (a b c d : ℕ) : (attainable a b c d).Nonempty := by
  refine ⟨0, (fun _ => 0), (fun _ => 0), ?_⟩
  simp [flow]

private theorem attainable_bddAbove (a b c d : ℕ) : BddAbove (attainable a b c d) := by
  refine ⟨min (a * d) (b * c), ?_⟩
  rintro r ⟨M, N, rfl⟩
  exact flow_rank_le_outer M N

private theorem attainable_finite (a b c d : ℕ) : (attainable a b c d).Finite :=
  (Set.finite_Iic (min (a * d) (b * c))).subset (by
    rintro r ⟨M, N, rfl⟩
    exact flow_rank_le_outer M N)

theorem QMaxFlow_attained (a b c d : ℕ) :
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ),
      (flow M N).rank = QMaxFlow a b c d :=
  (attainable_nonempty a b c d).csSup_mem (attainable_finite a b c d)

theorem rank_le_QMaxFlow {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) :
    (flow M N).rank ≤ QMaxFlow a b c d :=
  le_csSup (attainable_bddAbove a b c d) ⟨M, N, rfl⟩

private theorem QMaxFlow_le_outer (a b c d : ℕ) :
    QMaxFlow a b c d ≤ min (a * d) (b * c) := by
  apply csSup_le (attainable_nonempty a b c d)
  rintro r ⟨M, N, rfl⟩
  exact flow_rank_le_outer M N

private def cutLeft {K : Type*} [CommSemiring K] {a c d : ℕ}
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    Matrix (Fin a × Fin d) (Fin 3 × (Fin a × Fin c)) K :=
  fun i s => if i.1 = s.2.1 then N s.1 i.2 s.2.2 else 0

private def cutRight {K : Type*} [CommSemiring K] {a b c : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K) :
    Matrix (Fin 3 × (Fin a × Fin c)) (Fin b × Fin c) K :=
  fun s j => if s.2.2 = j.2 then M s.1 s.2.1 j.1 else 0

private theorem flow_factor {K : Type*} [CommSemiring K] {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    flow M N = cutLeft N * cutRight M := by
  ext i j
  change (∑ r : Fin 3, M r i.1 j.1 * N r i.2 j.2) =
    ∑ s : Fin 3 × (Fin a × Fin c),
      (if i.1 = s.2.1 then N s.1 i.2 s.2.2 else 0) *
      (if s.2.2 = j.2 then M s.1 s.2.1 j.1 else 0)
  simp [Fintype.sum_prod_type, mul_ite, eq_comm, mul_comm]

private theorem flow_rank_le_inner {K : Type*} [Field K] {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    (flow M N).rank ≤ 3 * a * c := by
  rw [flow_factor]
  exact (Matrix.rank_mul_le_left _ _).trans
    (by simpa [mul_assoc] using (cutLeft (a := a) N).rank_le_card_width)

theorem QMaxFlow_le_QMinCut (a b c d : ℕ) : QMaxFlow a b c d ≤ QMinCut a b c d := by
  refine le_min ?_ (QMaxFlow_le_outer a b c d)
  apply csSup_le (attainable_nonempty a b c d)
  rintro r ⟨M, N, rfl⟩
  exact flow_rank_le_inner M N

private theorem QMinCut_eq_outer {a b c d : ℕ} (_hb : b ≤ 3 * a) (hd : d ≤ 3 * c) :
    QMinCut a b c d = min (a * d) (b * c) := by
  apply min_eq_right
  exact (min_le_left _ _).trans (by nlinarith)

theorem cone_bounds {a b : ℕ} (ha : 0 < a)
    (h : a * a + b * b ≤ 3 * a * b) : b < 3 * a := by
  by_contra hb
  have hh : 3 * a ≤ b := by omega
  have hm : 3 * a * b ≤ b * b := by nlinarith
  nlinarith

theorem cone_QMinCut {a b c d : ℕ} (ha : 0 < a) (hc : 0 < c)
    (hab : a * a + b * b ≤ 3 * a * b)
    (hcd : c * c + d * d ≤ 3 * c * d) :
    QMinCut a b c d = min (a * d) (b * c) :=
  QMinCut_eq_outer (Nat.le_of_lt (cone_bounds ha hab))
    (Nat.le_of_lt (cone_bounds hc hcd))

end
section

private theorem algebraMap_mem_span {K L ι m : Type*} [Field K] [Field L] [Algebra K L]
    {v : ι → m → K} {x : m → K}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    (fun i => algebraMap K L (x i)) ∈
      Submodule.span L (Set.range (fun j i => algebraMap K L (v j i))) := by
  let f : (m → K) →ₗ[K] (m → L) :=
    LinearMap.pi fun i => (Algebra.linearMap K L).comp (LinearMap.proj i)
  let N := Submodule.span L (Set.range (fun j i => algebraMap K L (v j i)))
  apply (Submodule.image_span_subset f (Set.range v) (N.restrictScalars K)).mpr
    (fun y hy => ?_) ⟨x, hx, rfl⟩
  rcases hy with ⟨j, rfl⟩
  exact Submodule.subset_span ⟨j, rfl⟩

private theorem rank_map_algebraMap {K L m n : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype m] [Fintype n] (A : Matrix m n K) :
    (A.map (algebraMap K L)).rank = A.rank := by
  classical
  obtain ⟨ι, e, he, hspan, hli⟩ := exists_linearIndependent' K A.col
  let : Finite ι := Finite.of_injective e he
  let : Fintype ι := Fintype.ofFinite ι
  have hliL : LinearIndependent L ((A.map (algebraMap K L)).col ∘ e) := by
    exact linearIndependent_algebraMap_comp_iff.mpr hli
  have hspanL :
      Submodule.span L (Set.range ((A.map (algebraMap K L)).col ∘ e)) =
        Submodule.span L (Set.range (A.map (algebraMap K L)).col) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro x ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      have hj : A.col j ∈ Submodule.span K (Set.range (A.col ∘ e)) := by
        rw [hspan]
        exact Submodule.subset_span ⟨j, rfl⟩
      exact algebraMap_mem_span hj
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols,
    ← hspanL, ← hspan, finrank_span_eq_card hliL, finrank_span_eq_card hli]

private theorem flow_map {K L : Type*} [Field K] [Field L] [Algebra K L] {a b c d : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) K)
    (N : Fin 3 → Matrix (Fin d) (Fin c) K) :
    (flow M N).map (algebraMap K L) =
      flow (fun r => (M r).map (algebraMap K L))
        (fun r => (N r).map (algebraMap K L)) := by
  ext i j
  change algebraMap K L (∑ r : Fin 3, M r i.1 j.1 * N r i.2 j.2) =
    ∑ r : Fin 3, algebraMap K L (M r i.1 j.1) * algebraMap K L (N r i.2 j.2)
  simp only [map_sum, map_mul]

private theorem rational_witness_lower_bound {a b c d r : ℕ}
    (M : Fin 3 → Matrix (Fin a) (Fin b) ℚ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℚ) (hr : (flow M N).rank = r) :
    r ≤ QMaxFlow a b c d := by
  have hmap := rank_map_algebraMap (L := ℂ) (flow M N)
  rw [flow_map, hr] at hmap
  rw [← hmap]
  exact rank_le_QMaxFlow _ _

def RationalWitness (a b c d : ℕ) : Prop :=
  ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℚ)
    (N : Fin 3 → Matrix (Fin d) (Fin c) ℚ),
    (flow M N).rank = min (a * d) (b * c)

theorem rationalWitness_full_rank {a b c d : ℕ} (h : RationalWitness a b c d) :
    QMaxFlow a b c d = min (a * d) (b * c) := by
  obtain ⟨M, N, hr⟩ := h
  exact le_antisymm (QMaxFlow_le_outer a b c d) (rational_witness_lower_bound M N hr)

end
section

def BaseWitness : Prop :=
  ∀ a b c d : ℕ, 0 < a → a < b → b < 2 * a →
    0 < c → c < d → d < 2 * c → RationalWitness a b c d

def Castling : Prop :=
  ∀ a b c d : ℕ, a ≤ 3 * b → c ≤ 3 * d →
    (a * d : ℕ) - (QMaxFlow a b c d : ℤ) =
      (b * (3 * d - c) : ℕ) - (QMaxFlow b (3 * b - a) d (3 * d - c) : ℤ)

def WidthTwo : Prop :=
  ∀ a b c d : ℕ, 0 < a → a ≤ b → 0 < c → c ≤ d →
    (a = b ∨ c = d ∨ (2 * a ≤ b ∧ d ≤ 2 * c) ∨
      (b ≤ 2 * a ∧ 2 * c ≤ d)) → RationalWitness a b c d

end
section

def threeSlices {m n : Type*} (A B C : Matrix m n ℚ) (r : Fin 3) : Matrix m n ℚ :=
  if r = 0 then A else if r = 1 then B else C

lemma typed_three_slice_flow {I J K L : Type*}
    (A B C : Matrix I J ℚ) (D E F : Matrix L K ℚ) :
    (∑ r : Fin 3, kronecker (threeSlices A B C r) (threeSlices D E F r)) =
      kronecker A D + kronecker B E + kronecker C F := by
  simpa [threeSlices] using Fin.sum_univ_three
    (fun r => kronecker (threeSlices A B C r) (threeSlices D E F r))

private theorem flow_two {a b c d : ℕ}
    (A B : Matrix (Fin a) (Fin b) ℚ) (C D : Matrix (Fin d) (Fin c) ℚ) :
    flow ((threeSlices A B 0)) ((threeSlices C D 0)) = Matrix.kronecker A C + Matrix.kronecker B D := by
  unfold flow
  rw [typed_three_slice_flow]
  ext i j
  simp [Matrix.kronecker_apply]

def rectId (m n : ℕ) : Matrix (Fin m) (Fin n) ℚ :=
  (1 : Matrix ℕ ℕ ℚ).submatrix Fin.val Fin.val

private theorem rank_lower_of_identity_submatrix {m n t : Type*} [Fintype m] [Fintype n]
    [Fintype t] [DecidableEq t] (A : Matrix m n ℚ) (r : t → m) (s : t → n)
    (h : A.submatrix r s = 1) : Fintype.card t ≤ A.rank := by
  have hh := Matrix.rank_submatrix_le A r s
  rw [h, Matrix.rank_one] at hh
  exact hh

private theorem square_left {a c d : ℕ} (hcd : c ≤ d) : RationalWitness a a c d := by
  let M := (threeSlices (1 : Matrix (Fin a) (Fin a) ℚ) 0 0)
  let N := (threeSlices (rectId d c) 0 0)
  refine ⟨M, N, ?_⟩
  have hsub : (flow M N).submatrix
      (fun i : Fin a × Fin c => (i.1, Fin.castLE hcd i.2)) id = 1 := by
    ext i j
    by_cases h1 : i.1.val = j.1.val <;> by_cases h2 : i.2.val = j.2.val <;>
      simp [M, N, flow_two, rectId, Matrix.one_apply, Prod.ext_iff, Fin.ext_iff, h1, h2]
  have hlow : a * c ≤ (flow M N).rank := by
    simpa using rank_lower_of_identity_submatrix (flow M N) _ _ hsub
  have hcut : min (a * d) (a * c) = a * c := min_eq_right (Nat.mul_le_mul_left a hcd)
  rw [hcut]
  exact le_antisymm ((flow_rank_le_outer M N).trans (min_le_right _ _)) hlow

private theorem square_right {a b c : ℕ} (hab : a ≤ b) : RationalWitness a b c c := by
  let M := (threeSlices (rectId a b) 0 0)
  let N := (threeSlices (1 : Matrix (Fin c) (Fin c) ℚ) 0 0)
  refine ⟨M, N, ?_⟩
  have hsub : (flow M N).submatrix id
      (fun i : Fin a × Fin c => (Fin.castLE hab i.1, i.2)) = 1 := by
    ext i j
    by_cases h1 : i.1.val = j.1.val <;> by_cases h2 : i.2.val = j.2.val <;>
      simp [M, N, flow_two, rectId, Matrix.one_apply, Prod.ext_iff, Fin.ext_iff, h1, h2]
  have hlow : a * c ≤ (flow M N).rank := by
    simpa using rank_lower_of_identity_submatrix (flow M N) _ _ hsub
  have hcut : min (a * c) (b * c) = a * c := min_eq_left (Nat.mul_le_mul_right c hab)
  rw [hcut]
  exact le_antisymm ((flow_rank_le_outer M N).trans (min_le_left _ _)) hlow

private def mixedColumns {a b c d : ℕ} (hb : 2 * a ≤ b) (hd : d ≤ 2 * c)
    (i : Fin a × Fin d) : Fin b × Fin c :=
  if hk : i.2.val < c then
    (⟨i.1.val, by omega⟩, ⟨i.2.val, hk⟩)
  else
    (⟨a + i.1.val, by omega⟩, ⟨i.2.val - c, by omega⟩)

private theorem mixed_left {a b c d : ℕ} (hb : 2 * a ≤ b) (hd : d ≤ 2 * c) :
    RationalWitness a b c d := by
  let M0 := rectId a b
  let M1 : Matrix (Fin a) (Fin b) ℚ := fun i j => if a + i.val = j.val then 1 else 0
  let N0 := rectId d c
  let N1 : Matrix (Fin d) (Fin c) ℚ := fun k h => if k.val = c + h.val then 1 else 0
  let M := (threeSlices M0 M1 0)
  let N := (threeSlices N0 N1 0)
  refine ⟨M, N, ?_⟩
  have hsub : (flow M N).submatrix id (mixedColumns hb hd) = 1 := by
    change (flow ((threeSlices M0 M1 0)) ((threeSlices N0 N1 0))).submatrix id (mixedColumns hb hd) = 1
    rw [flow_two]
    ext i j
    have ha0 : a ≠ 0 := by have hi := i.1.isLt; omega
    by_cases hk : j.2.val < c
    · have hfalse : ¬ (a + i.1.val = j.1.val) := by omega
      by_cases h1 : i.1.val = j.1.val <;> by_cases h2 : i.2.val = j.2.val <;>
        simp [M0, M1, N0, N1, mixedColumns, hk, hfalse,
          rectId, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply,
          Prod.ext_iff, Fin.ext_iff, ha0, h1, h2]
    · have hfalse : ¬ (i.1.val = a + j.1.val) := by omega
      have hcancel : c + (j.2.val - c) = j.2.val := by omega
      by_cases h1 : i.1.val = j.1.val <;> by_cases h2 : i.2.val = j.2.val <;>
        simp [M0, M1, N0, N1, mixedColumns, hk, hfalse, hcancel,
          rectId, Matrix.kronecker, Matrix.kroneckerMap, Matrix.one_apply,
          Prod.ext_iff, Fin.ext_iff, ha0, h1, h2]
  have hlow : a * d ≤ (flow M N).rank := by
    simpa using rank_lower_of_identity_submatrix (flow M N) _ _ hsub
  have hcut : min (a * d) (b * c) = a * d := min_eq_left (by nlinarith)
  rw [hcut]
  exact le_antisymm ((flow_rank_le_outer M N).trans (min_le_left _ _)) hlow

theorem witness_swap {a b c d : ℕ} (h : RationalWitness a b c d) :
    RationalWitness c d a b := by
  obtain ⟨M, N, hr⟩ := h
  refine ⟨fun r => (N r).transpose, fun r => (M r).transpose, ?_⟩
  have heq : flow (fun r => (N r).transpose) (fun r => (M r).transpose) =
      (flow M N).transpose.submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _) := by
    ext i j
    change (∑ r : Fin 3, N r j.1 i.1 * M r j.2 i.2) =
      ∑ r : Fin 3, M r j.2 i.2 * N r j.1 i.1
    simp only [mul_comm]
  rw [heq, Matrix.rank_submatrix, Matrix.rank_transpose, hr]
  simp only [mul_comm, min_comm]

private theorem mixed_right {a b c d : ℕ} (hb : b ≤ 2 * a) (hd : 2 * c ≤ d) :
    RationalWitness a b c d := by
  exact witness_swap (mixed_left hd hb)

theorem widthTwo_proved : WidthTwo := by
  intro a b c d ha hab hc hcd h
  rcases h with h | h | h | h
  · subst b
    exact square_left hcd
  · subst d
    exact square_right hab
  · exact mixed_left h.1 h.2
  · exact mixed_right h.1 h.2

end

end D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
