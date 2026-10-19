/- GID: D5/S3/Quantum/Matrix/LinGProperty/Normalization
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinGProperty/Normalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/CartesianVariance]
   utility: none
   digest: Trace normalization and zero-block reduction for the trace augmentation map. -/

import D5.S3.Quantum.Matrix.CartesianVariance

/-! The trace augmentation map and its positive and degenerate input cases. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.LinGProperty

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Trace augmentation with a real parameter. -/
def phi {n : ℕ} (c : ℝ) (T : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := T + ((c : ℂ) * T.trace) • 1

private theorem diagonal_blocks_posSemidef {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (h : (fromBlocks A X Xᴴ B).PosSemidef) : A.PosSemidef ∧ B.PosSemidef := by
  constructor
  · have he : (fromBlocks A X Xᴴ B).submatrix Sum.inl Sum.inl = A := by ext i j; rfl
    rw [← he]
    exact h.submatrix Sum.inl
  · have he : (fromBlocks A X Xᴴ B).submatrix Sum.inr Sum.inr = B := by ext i j; rfl
    rw [← he]
    exact h.submatrix Sum.inr

/-- A zero diagonal block in a positive block matrix forces its off-diagonal block to vanish. -/
theorem offDiagonal_eq_zero {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (h : (fromBlocks A X Xᴴ B).PosSemidef) (hz : A = 0 ∨ B = 0) : X = 0 := by
  ext i j
  have hb := CartesianVariance.psd_entry_bound h (Sum.inl i) (Sum.inr j)
  have hzero : Complex.normSq (X i j) ≤ 0 := by
    rcases hz with rfl | rfl <;> simpa using hb
  exact Complex.normSq_eq_zero.mp (le_antisymm hzero (Complex.normSq_nonneg _))

/-- Nonzero positive matrices have strictly positive real trace. -/
theorem positive_trace {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hne : A ≠ 0) : 0 < A.trace.re := by
  have hnonneg : 0 ≤ A.trace.re := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  apply lt_of_le_of_ne hnonneg
  intro hz
  have him : A.trace.im = 0 := (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
  exact hne (hA.trace_eq_zero_iff.mp (Complex.ext hz.symm him))

/-- Trace augmentation is positive definite on every nonzero positive input. -/
theorem phi_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hne : A ≠ 0) {c : ℝ} (hc : 1 ≤ c) :
    (phi c A).PosDef := by
  have ht : A.trace = (A.trace.re : ℂ) :=
    Complex.ext (by simp) (by simpa using (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm)
  have hp : (0 : ℝ) < c * A.trace.re := mul_pos (by linarith) (positive_trace hA hne)
  have hI : (((c * A.trace.re : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hp)
  unfold phi
  rw [ht, ← Complex.ofReal_mul]
  exact Matrix.PosDef.posSemidef_add hA hI

/-- Real scaling commutes with trace augmentation. -/
theorem phi_smul {n : ℕ} (c r : ℝ) (T : Matrix (Fin n) (Fin n) ℂ) :
    phi c (r • T) = r • phi c T := by
  simp only [phi, Matrix.trace_smul, smul_add, smul_smul]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  push_cast
  ring

/-- Real block-diagonal congruence rescales both diagonal blocks and their common cross block. -/
theorem block_scale_posSemidef {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (r s : ℝ) :
    (fromBlocks ((r*r) • A) ((r*s) • X) ((r*s) • X)ᴴ ((s*s) • B)).PosSemidef := by
  let D := fromBlocks (r • (1 : Matrix (Fin n) (Fin n) ℂ)) 0 0
    (s • (1 : Matrix (Fin n) (Fin n) ℂ))
  have h := hW.mul_mul_conjTranspose_same D
  simpa [D, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, mul_comm, mul_left_comm, mul_assoc] using h

end D5.S3.Quantum.Matrix.LinGProperty
