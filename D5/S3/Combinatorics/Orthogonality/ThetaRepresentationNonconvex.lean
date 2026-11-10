/- GID: D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex
   mirror-E: none(waiver:source-only-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.claim; result=D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.result; claim=D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex.claim
   digest: The trace-two orthonormal representation set of the five-cycle is not convex. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators

namespace D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex

/-- The source's full set: a common real PSD contraction of trace exactly `k`,
and a common family of unit vectors orthogonal on edges of `G`, in dimension `|V|`. -/
def representationSet {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℝ) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∃ M : Matrix V V ℝ,
    M.PosSemidef ∧ (1 - M).PosSemidef ∧ M.trace = k ∧
    ∃ u : V → V → ℝ,
      (∀ i, u i ⬝ᵥ u i = 1) ∧
      (∀ i j, G.Adj i j → u i ⬝ᵥ u j = 0) ∧
      (∀ i, x i = u i ⬝ᵥ (M *ᵥ u i))}

/-- The affirmative answer to the first clause of Question (iv),
for every positive feasible real parameter and every finite simple graph. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], 1 ≤ Fintype.card V →
    ∀ (G : SimpleGraph V) (k : ℝ), 0 < k → k ≤ Fintype.card V →
      Convex ℝ (representationSet G k)

private theorem fixed_of_one {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hC : (1 - M).PosSemidef)
    (a : V → ℝ) (ha : a ⬝ᵥ a = 1) (hq : a ⬝ᵥ (M *ᵥ a) = 1) :
    M *ᵥ a = a := by
  have hz : star a ⬝ᵥ ((1 - M) *ᵥ a) = 0 := by
    simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub, ha, hq, sub_self]
  have hk := (hC.dotProduct_mulVec_zero_iff (x := a)).mp hz
  simp only [sub_mulVec, one_mulVec, sub_eq_zero] at hk
  exact hk.symm

private theorem saturated_projection {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.PosSemidef) (hC : (1 - M).PosSemidef)
    (ht : M.trace = 2) (a b : V → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    (hqa : a ⬝ᵥ (M *ᵥ a) = 1) (hqb : b ⬝ᵥ (M *ᵥ b) = 1) :
    M = vecMulVec a a + vecMulVec b b := by
  have hMa := fixed_of_one M hC a ha hqa
  have hMb := fixed_of_one M hC b hb hqb
  have hs : Mᵀ = M := (Matrix.isHermitian_iff_isSymm.mp hM.1)
  have haM : a ᵥ* M = a := by rw [← hs, vecMul_transpose, hMa]
  have hbM : b ᵥ* M = b := by rw [← hs, vecMul_transpose, hMb]
  have hba : b ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact hab
  let P := vecMulVec a a + vecMulVec b b
  have hP : P.IsHermitian := by
    simp only [P, IsHermitian, conjTranspose_add, conjTranspose_vecMulVec, star_trivial]
  have hpos : (M - P).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hM.1.sub hP)
    intro w
    let r := w - (a ⬝ᵥ w) • a - (b ⬝ᵥ w) • b
    have hr := hM.dotProduct_mulVec_nonneg r
    have heq : star w ⬝ᵥ ((M - P) *ᵥ w) = star r ⬝ᵥ (M *ᵥ r) := by
      simp only [r, P, star_trivial, sub_mulVec, add_mulVec,
        vecMulVec_mulVec, mulVec_sub, mulVec_smul, hMa, hMb,
        dotProduct_sub, sub_dotProduct, dotProduct_add, dotProduct_smul,
        smul_dotProduct, dotProduct_mulVec, sub_vecMul, smul_vecMul,
        haM, hbM, ha, hb, hab, hba,
        op_smul_eq_smul]
      rw [dotProduct_comm w a, dotProduct_comm w b]
      ring
    rw [heq]
    exact hr
  have hz : (M - P).trace = 0 := by
    simp only [trace_sub, P, trace_add, trace_vecMulVec, ht, ha, hb]
    norm_num
  exact sub_eq_zero.mp ((hpos.trace_eq_zero_iff).mp hz)

theorem dot_cauchy {V : Type} [Fintype V] (v w : V → ℝ) :
    (v ⬝ᵥ w) ^ 2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
  simpa only [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w

private def residual {V : Type} [Fintype V] (a b w : V → ℝ) : V → ℝ :=
  w - (a ⬝ᵥ w) • a - (b ⬝ᵥ w) • b

private theorem residual_pair {V : Type} [Fintype V]
    (a b w z : V → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (hab : a ⬝ᵥ b = 0) :
    residual a b w ⬝ᵥ residual a b z =
      w ⬝ᵥ z - (a ⬝ᵥ w) * (a ⬝ᵥ z) - (b ⬝ᵥ w) * (b ⬝ᵥ z) := by
  have hba : b ⬝ᵥ a = 0 := by rw [dotProduct_comm]; exact hab
  simp only [residual, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, ha, hb, hab, hba]
  rw [dotProduct_comm w a, dotProduct_comm w b]
  ring

private def cycleFive : SimpleGraph (Fin 5) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
    (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0)
  symm := ⟨by intro i j h; tauto⟩
  loopless := ⟨by intro i h; rcases h with h | h | h | h <;> omega⟩

private instance : DecidableRel cycleFive.Adj := by
  unfold cycleFive
  infer_instance

private def missingPoint : Fin 5 → ℝ := ![2 / 3, 2 / 3, 2 / 3, 1, 1]

private theorem missingPoint_not_mem : missingPoint ∉ representationSet cycleFive 2 := by
  rintro ⟨_, M, hM, hC, ht, u, hu, he, hx⟩
  have h34 : u 3 ⬝ᵥ u 4 = 0 := he 3 4 (by decide)
  have h40 : u 4 ⬝ᵥ u 0 = 0 := he 4 0 (by decide)
  have h32 : u 3 ⬝ᵥ u 2 = 0 := he 3 2 (by decide)
  have h01 : u 0 ⬝ᵥ u 1 = 0 := he 0 1 (by decide)
  have h21 : u 2 ⬝ᵥ u 1 = 0 := he 2 1 (by decide)
  have hp : M = vecMulVec (u 3) (u 3) + vecMulVec (u 4) (u 4) :=
    saturated_projection M hM hC ht (u 3) (u 4) (hu 3) (hu 4) h34
      (by simpa [missingPoint] using (hx 3).symm)
      (by simpa [missingPoint] using (hx 4).symm)
  have hq (i : Fin 5) :
      (u 3 ⬝ᵥ u i) ^ 2 + (u 4 ⬝ᵥ u i) ^ 2 = missingPoint i := by
    rw [hx i, hp]
    simp only [add_mulVec, vecMulVec_mulVec, dotProduct_add,
      dotProduct_smul, op_smul_eq_smul]
    rw [dotProduct_comm (u i) (u 3), dotProduct_comm (u i) (u 4)]
    ring
  have hn (i : Fin 5) :
      residual (u 3) (u 4) (u i) ⬝ᵥ residual (u 3) (u 4) (u i) =
        1 - missingPoint i := by
    rw [residual_pair _ _ _ _ (hu 3) (hu 4) h34, hu i]
    nlinarith [hq i]
  have h0 : (u 3 ⬝ᵥ u 0) ^ 2 = 2 / 3 := by
    have := hq 0
    simpa [missingPoint, h40] using this
  have h2 : (u 4 ⬝ᵥ u 2) ^ 2 = 2 / 3 := by
    have := hq 2
    simpa [missingPoint, h32] using this
  have h1 : (u 3 ⬝ᵥ u 1) ^ 2 + (u 4 ⬝ᵥ u 1) ^ 2 = 2 / 3 := by
    simpa [missingPoint] using hq 1
  have hc0 := dot_cauchy (residual (u 3) (u 4) (u 0))
    (residual (u 3) (u 4) (u 1))
  have hc2 := dot_cauchy (residual (u 3) (u 4) (u 2))
    (residual (u 3) (u 4) (u 1))
  rw [hn 0, hn 1, residual_pair _ _ _ _ (hu 3) (hu 4) h34] at hc0
  rw [hn 2, hn 1, residual_pair _ _ _ _ (hu 3) (hu 4) h34] at hc2
  simp only [h01, h21, h40, h32, zero_mul, sub_zero,
    zero_sub, neg_sq, mul_pow] at hc0 hc2
  simp [missingPoint, h0, h2] at hc0 hc2
  nlinarith

private def coordinate (i : Fin 5) : Fin 5 → ℝ := Pi.single i 1

private def endpointA : Fin 5 → ℝ := ![0, 1, 1, 1, 1]
private def endpointB : Fin 5 → ℝ := ![1, 0, 1, 1, 1]
private def endpointC : Fin 5 → ℝ := ![1, 1, 0, 1, 1]

private def diagonalProjection : Matrix (Fin 5) (Fin 5) ℝ :=
  diagonal ![1, 1, 0, 0, 0]

private theorem coordinate_realization (f : Fin 5 → Fin 5) (x : Fin 5 → ℝ)
    (hf : ∀ i j, cycleFive.Adj i j → f i ≠ f j)
    (hx : ∀ i, x i = (![1, 1, 0, 0, 0] : Fin 5 → ℝ) (f i)) :
    x ∈ representationSet cycleFive 2 := by
  have hd : diagonalProjection.PosSemidef := by
    rw [diagonalProjection, posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  have hc : (1 - diagonalProjection).PosSemidef := by
    rw [diagonalProjection, ← diagonal_one, diagonal_sub, posSemidef_diagonal_iff]
    intro i
    fin_cases i <;> norm_num
  refine ⟨?_, diagonalProjection, hd, hc, ?_, fun i => coordinate (f i), ?_, ?_, ?_⟩
  · intro i
    rw [hx i]
    generalize f i = j
    fin_cases j <;> first | exact (zero_le_one : (0 : ℝ) ≤ 1) | exact le_rfl
  · norm_num [diagonalProjection, trace_diagonal, Fin.sum_univ_succ]
  · intro i
    simp [coordinate]
  · intro i j hij
    simp [coordinate, Pi.single_eq_of_ne (hf i j hij).symm]
  · intro i
    rw [hx i]
    simp [coordinate, diagonalProjection]

private theorem endpoints_mem :
    endpointA ∈ representationSet cycleFive 2 ∧
    endpointB ∈ representationSet cycleFive 2 ∧
    endpointC ∈ representationSet cycleFive 2 := by
  refine ⟨coordinate_realization ![2, 0, 1, 0, 1] endpointA (by decide) ?_,
    coordinate_realization ![1, 2, 0, 1, 0] endpointB (by decide) ?_,
    coordinate_realization ![0, 1, 2, 0, 1] endpointC (by decide) ?_⟩
  all_goals
    intro i
    fin_cases i <;> rfl

private theorem nonconvex_cycleFive : ¬ Convex ℝ (representationSet cycleFive 2) := by
  intro h
  have ha := endpoints_mem.1
  have hb := endpoints_mem.2.1
  have hc := endpoints_mem.2.2
  have hbc := (convex_iff_add_mem.mp h) hb hc
    (a := (1 / 2 : ℝ)) (b := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have habc := (convex_iff_add_mem.mp h) ha hbc
    (a := (1 / 3 : ℝ)) (b := 2 / 3) (by norm_num) (by norm_num) (by norm_num)
  apply missingPoint_not_mem
  convert habc using 1
  ext i
  fin_cases i <;> norm_num [missingPoint, endpointA, endpointB, endpointC]

/-- The five-cycle at `k = 2` refutes the universal convexity assertion. -/
theorem result : ¬ claim := by
  intro h
  exact nonconvex_cycleFive (h (Fin 5) (by norm_num) cycleFive 2
    (by norm_num) (by norm_num))

#print axioms result

end D5.S3.Combinatorics.Orthogonality.ThetaRepresentationNonconvex
