/- GID: D5/S3/Quantum/Divergence/SpectralKlein
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SpectralKlein
   mirror-E: none(waiver:general-matrix-inequality)
   anchors: []
   digest: Derive the noncommuting finite-matrix Klein inequality from actual spectral bases and scalar logarithm convexity. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Tactic

/-!
The two eigenbases are obtained by the matrix spectral theorem. Their overlap
matrix is proved doubly stochastic from the actual unitary identities. The
relative-entropy lower bound is not a hypothesis. The first matrix may be
singular; the reference is positive definite, so the finite CFC trace-log
expression has the correct support semantics. No result for unsupported
pairs, measurement DPI, or quantum Pinsker is inferred from this theorem.

Pinned sources inspected: Mathlib v4.33.0 Matrix/Spectrum,
Matrix/HermitianFunctionalCalculus, Matrix/PosDef, and CFC ExpLog/Basic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Divergence.SpectralKlein

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix Unitary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An actual unitary spectral synthesis, on the full complex matrix algebra. -/
def spectral (U : unitary (Matrix n n ℂ)) (a : n → ℝ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * Matrix.diagonal (fun i => (a i : ℂ)) * star (U : Matrix n n ℂ)

/-- The squared overlap of the two actual orthonormal coordinate systems. -/
def overlap (W : unitary (Matrix n n ℂ)) (i j : n) : ℝ :=
  Complex.normSq ((W : Matrix n n ℂ) i j)

theorem overlap_nonneg (W : unitary (Matrix n n ℂ)) (i j : n) :
    0 ≤ overlap W i j := Complex.normSq_nonneg _

theorem overlap_row_sum (W : unitary (Matrix n n ℂ)) (i : n) :
    ∑ j, overlap W i j = 1 := by
  have h := congrArg (fun A : Matrix n n ℂ => (A i i).re)
    (Unitary.coe_mul_star_self W)
  simpa [overlap, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.mul_re, Complex.normSq_apply] using h

theorem overlap_col_sum (W : unitary (Matrix n n ℂ)) (j : n) :
    ∑ i, overlap W i j = 1 := by
  have h := congrArg (fun A : Matrix n n ℂ => (A j j).re)
    (Unitary.coe_star_mul_self W)
  simpa [overlap, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Complex.mul_re, Complex.normSq_apply] using h

private theorem weighted_rows (W : unitary (Matrix n n ℂ)) (f : n → ℝ) :
    (∑ i, ∑ j, overlap W i j * f i) = ∑ i, f i := by
  simp_rw [← Finset.sum_mul, overlap_row_sum, one_mul]

private theorem weighted_cols (W : unitary (Matrix n n ℂ)) (f : n → ℝ) :
    (∑ i, ∑ j, overlap W i j * f j) = ∑ j, f j := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, overlap_col_sum, one_mul]

theorem spectral_mul_same (U : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    spectral U a * spectral U b = spectral U (fun i => a i * b i) := by
  unfold spectral
  have h := Unitary.coe_star_mul_self U
  simp only [mul_assoc, h, one_mul, ← mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
    Matrix.diagonal_mul_diagonal, Complex.ofReal_mul]

/-- Trace is computed in the actual finite-dimensional representation. -/
theorem trace_spectral (U : unitary (Matrix n n ℂ)) (a : n → ℝ) :
    (Matrix.trace (spectral U a)).re = ∑ i, a i := by
  unfold spectral
  rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
    Matrix.trace_diagonal]
  simp

private theorem trace_diagonal_overlap (W : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    (Matrix.trace
      (Matrix.diagonal (fun i => (a i : ℂ)) * (W : Matrix n n ℂ) *
       Matrix.diagonal (fun j => (b j : ℂ)) * star (W : Matrix n n ℂ))).re =
      ∑ i, ∑ j, a i * b j * overlap W i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [overlap, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  <;> ring

/-- Cross terms use the overlap of two independently chosen spectral bases.
No simultaneous diagonalization or commutation hypothesis is imposed. -/
theorem trace_spectral_mul (U V : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    (Matrix.trace (spectral U a * spectral V b)).re =
      ∑ i, ∑ j, a i * b j * overlap (star U * V) i j := by
  have hcycle : Matrix.trace (spectral U a * spectral V b) =
      Matrix.trace (Matrix.diagonal (fun i => (a i : ℂ)) *
        ((star U * V : unitary (Matrix n n ℂ)) : Matrix n n ℂ) *
        Matrix.diagonal (fun j => (b j : ℂ)) *
        star (((star U * V : unitary (Matrix n n ℂ)) : Matrix n n ℂ))) := by
    have h := Matrix.trace_mul_comm (U : Matrix n n ℂ)
      (Matrix.diagonal (fun i => (a i : ℂ)) * star (U : Matrix n n ℂ) *
        (V : Matrix n n ℂ) * Matrix.diagonal (fun j => (b j : ℂ)) * star (V : Matrix n n ℂ))
    simpa only [spectral, mul_assoc, SetLike.coe_mul, Unitary.coe_star, star_mul,
      star_star] using h
  rw [hcycle]
  exact trace_diagonal_overlap (star U * V) a b

theorem matrix_eq_spectral {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = spectral hA.eigenvectorUnitary hA.eigenvalues := by
  simpa only [spectral, Unitary.conjStarAlgAut_apply, Function.comp_def] using hA.spectral_theorem

theorem log_eq_spectral {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    CFC.log A = spectral hA.eigenvectorUnitary (fun i => Real.log (hA.eigenvalues i)) := by
  simpa only [CFC.log, Matrix.IsHermitian.cfc, spectral,
    Unitary.conjStarAlgAut_apply, Function.comp_def]
    using hA.cfc_eq Real.log

/-- Scalar Klein inequality, including the zero eigenvalue of the first state. -/
theorem scalar_klein (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * Real.log a - a * Real.log b - a + b := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0]
    simpa using hb.le
  · have ht : a * (Real.log b - Real.log a) ≤ b - a := by
      calc
        a * (Real.log b - Real.log a) = a * Real.log (b / a) := by
          rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha0)]
        _ ≤ a * (b / a - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha0)) ha
        _ = b - a := by field_simp [ne_of_gt ha0]; ring
    nlinarith

private theorem weighted_klein_identity
    (W : unitary (Matrix n n ℂ)) (a b : n → ℝ) :
    (∑ i, a i * Real.log (a i)) -
        (∑ i, ∑ j, a i * Real.log (b j) * overlap W i j) -
        (∑ i, a i) + (∑ j, b j) =
      ∑ i, ∑ j, overlap W i j *
        (a i * Real.log (a i) - a i * Real.log (b j) - a i + b j) := by
  have hc : (∑ i, ∑ j, overlap W i j * (a i * Real.log (b j))) =
      ∑ i, ∑ j, a i * Real.log (b j) * overlap W i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [weighted_rows W (fun i => a i * Real.log (a i)),
    weighted_rows W a, weighted_cols W b, hc]

/-- Finite-dimensional Klein inequality for possibly singular A and faithful B.
The CFC logarithms are the actual matrix logarithms, not unspecified functions. -/
theorem klein_trace_nonneg (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosDef) :
    0 ≤ (Matrix.trace (A * (CFC.log A - CFC.log B) - A + B)).re := by
  let U := hA.isHermitian.eigenvectorUnitary
  let V := hB.isHermitian.eigenvectorUnitary
  let a := hA.isHermitian.eigenvalues
  let b := hB.isHermitian.eigenvalues
  have ha : ∀ i, 0 ≤ a i := hA.eigenvalues_nonneg
  have hb : ∀ i, 0 < b i := hB.eigenvalues_pos
  have he : (Matrix.trace (A * (CFC.log A - CFC.log B) - A + B)).re =
      ∑ i, ∑ j, overlap (star U * V) i j *
        (a i * Real.log (a i) - a i * Real.log (b j) - a i + b j) := by
    rw [Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
      Complex.add_re, Complex.sub_re, Complex.sub_re,
      log_eq_spectral hA.isHermitian, log_eq_spectral hB.isHermitian,
      matrix_eq_spectral hA.isHermitian, matrix_eq_spectral hB.isHermitian,
      spectral_mul_same, trace_spectral, trace_spectral_mul, trace_spectral, trace_spectral]
    exact weighted_klein_identity (star U * V) a b
  rw [he]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (overlap_nonneg _ i j) (scalar_klein (a i) (b j) (ha i) (hb j))))

/-- Nonnegativity for normalized noncommuting density matrices with faithful reference. -/
theorem faithful_relative_entropy_nonneg (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosDef)
    (htrA : Matrix.trace A = 1) (htrB : Matrix.trace B = 1) :
    0 ≤ (Matrix.trace (A * (CFC.log A - CFC.log B))).re := by
  have h := klein_trace_nonneg A B hA hB
  simpa only [Matrix.trace_add, Matrix.trace_sub, htrA, htrB,
    sub_add_cancel] using h

#print axioms overlap_row_sum
#print axioms trace_spectral_mul
#print axioms klein_trace_nonneg
#print axioms faithful_relative_entropy_nonneg
end D5.S3.Quantum.Divergence.SpectralKlein
