/- GID: D5/S3/Quantum/Measurement/Auric/RootTrace
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/RootTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace square root under averaging with a unitary conjugate. -/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Matrix.Block

/-! # Trace square root under averaging with a unitary conjugate -/

@[expose] public section

namespace D5.S3.Quantum.Measurement.Auric.RootTrace

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem sqrt_star_conjugate (A U : Matrix n n ℂ) (hA : 0 ≤ A)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    CFC.sqrt (star U * A * U) = star U * CFC.sqrt A * U := by
  apply CFC.sqrt_unique
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U (star U), Matrix.mem_unitaryGroup_iff.mp hU]
    simp only [Matrix.one_mul, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (star U), CFC.sqrt_mul_sqrt_self A hA]
  · exact star_left_conjugate_nonneg (CFC.sqrt_nonneg A) U

/-- Pinching by a unitary sign matrix increases the trace of the square
root. Averaging with any unitary conjugate obeys the same bound. -/
theorem trace_sqrt_le_trace_sqrt_unitary_average (A U : Matrix n n ℂ) (hA : 0 ≤ A)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    (CFC.sqrt A).trace.re ≤
      (CFC.sqrt ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • (star U * A * U))).trace.re := by
  have hB := star_left_conjugate_nonneg hA U
  have h := (CFC.concaveOn_sqrt (A := Matrix n n ℂ)).2 hA hB
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have htrace := (Complex.le_def.mp
    ((Matrix.tracePositiveLinearMap n ℝ ℂ).monotone h)).1
  have hsame : (CFC.sqrt (star U * A * U)).trace = (CFC.sqrt A).trace := by
    rw [sqrt_star_conjugate A U hA hU, Matrix.trace_mul_cycle,
      Matrix.mem_unitaryGroup_iff.mp hU, Matrix.one_mul]
  change ((1 / 2 : ℝ) • CFC.sqrt A + (1 / 2 : ℝ) • (CFC.sqrt (star U * A * U))).trace.re ≤
    (CFC.sqrt ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • (star U * A * U))).trace.re at htrace
  simp only [Matrix.tracePositiveLinearMap_apply, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.smul_re, smul_eq_mul, hsame] at htrace
  linarith

variable {m : Type*} [Fintype m] [DecidableEq m]

private theorem posSemidef_direct_sum (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (fromBlocks A 0 0 B).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · ext (i | i) (j | j) <;> simp only [conjTranspose_apply, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, star_zero] <;>
      first | rfl | exact congrFun (congrFun hA.1.eq _ ) _ |
        exact congrFun (congrFun hB.1.eq _ ) _
  · intro x
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add]
    change 0 ≤ star x ⬝ᵥ Sum.elim (A *ᵥ (x ∘ Sum.inl)) (B *ᵥ (x ∘ Sum.inr))
    have hsplit : star x = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) := by
      ext (i | i) <;> rfl
    rw [hsplit, sumElim_dotProduct_sumElim]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hB.dotProduct_mulVec_nonneg _)

/-- The positive square root acts separately on orthogonal diagonal blocks. -/
theorem sqrt_direct_sum (A : Matrix n n ℂ) (B : Matrix m m ℂ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    CFC.sqrt (fromBlocks A 0 0 B) = fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) := by
  apply CFC.sqrt_unique
  · simp [fromBlocks_multiply, CFC.sqrt_mul_sqrt_self A hA, CFC.sqrt_mul_sqrt_self B hB]
  · exact (posSemidef_direct_sum _ _ (CFC.sqrt_nonneg A).posSemidef
      (CFC.sqrt_nonneg B).posSemidef).nonneg

/-- Pinching positive coherences between two possibly unequal finite blocks
upper bounds the trace square root by the sum of the diagonal contributions. -/
theorem trace_sqrt_le_of_two_blocks (A : Matrix n n ℂ) (B : Matrix n m ℂ)
    (C : Matrix m n ℂ) (D : Matrix m m ℂ)
    (h : 0 ≤ fromBlocks A B C D) :
    (CFC.sqrt (fromBlocks A B C D)).trace.re ≤
      (CFC.sqrt A).trace.re + (CFC.sqrt D).trace.re := by
  let U := fromBlocks (1 : Matrix n n ℂ) 0 0 (-1 : Matrix m m ℂ)
  have huStar : star U = U := by
    ext (i | i) (j | j) <;> simp [U, Matrix.star_eq_conjTranspose, conjTranspose_apply, one_apply]
    all_goals split_ifs <;> simp_all [eq_comm]
  have huSq : U * U = 1 := by
    simp [U, fromBlocks_multiply, fromBlocks_one]
  have hu : U ∈ unitaryGroup (n ⊕ m) ℂ :=
    Matrix.mem_unitaryGroup_iff.2 (by rw [huStar, huSq])
  have hconj : star U * fromBlocks A B C D * U = fromBlocks A (-B) (-C) D := by
    rw [huStar]
    simp [U, fromBlocks_multiply]
  have hpinch : (1 / 2 : ℝ) • fromBlocks A B C D +
      (1 / 2 : ℝ) • (star U * fromBlocks A B C D * U) = fromBlocks A 0 0 D := by
    rw [hconj, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    ext (i | i) (j | j) <;> simp [smul_eq_mul] <;> ring
  have htrace := trace_sqrt_le_trace_sqrt_unitary_average (fromBlocks A B C D) U h hu
  have hA : 0 ≤ A := by
    have he := h.posSemidef.submatrix (Sum.inl : n → n ⊕ m)
    change A.PosSemidef at he
    exact he.nonneg
  have hD : 0 ≤ D := by
    have he := h.posSemidef.submatrix (Sum.inr : m → n ⊕ m)
    change D.PosSemidef at he
    exact he.nonneg
  rw [hpinch, sqrt_direct_sum A D hA hD] at htrace
  simpa [Matrix.trace, Fintype.sum_sum_type] using htrace

end D5.S3.Quantum.Measurement.Auric.RootTrace
