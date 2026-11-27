/- GID: D5/S3/Quantum/Foundation/PowersStormer
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/PowersStormer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite matrix Powers–Størmer inequality and centered sandwich continuity. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import D5.S3.Quantum.Matrix.UniformVarianceTraceBound
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.Commutator
import Mathlib.Basic.Real.Sign

compile_only_with_mathlib

/-!
The finite complex-matrix form of the Powers–Størmer inequality
(Powers and Størmer, *Communications in Mathematical Physics* 16, 1–33,
Lemma 4.1, DOI 10.1007/BF01645492) controls the centered sandwich map
on density matrices, including singular states.
-/

noncomputable section
set_option autoImplicit false

namespace D5.S3.Quantum.Foundation.PowersStormer

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg traceNorm_add_le)
open D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability (entryNormSq_eq_hs_sq)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM (traceNorm_mul_le_hsSq)
open D5.S3.Quantum.Analysis.RefinedBMVNearScalarCommutator (frobenius_mul_le_op)

variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
private theorem sign_test_le_traceNorm (U : Matrix.unitaryGroup n ℂ) (d : n → ℝ)
    (X : Matrix n n ℂ) :
    ((U.val * Matrix.diagonal (fun i => (Real.sign (d i) : ℂ)) * U.valᴴ) * X).trace.re ≤
      traceNorm X := by
  let T : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sign (d i) : ℂ))
  let S := U.val * T * U.valᴴ
  change (S * X).trace.re ≤ traceNorm X
  have hS : ‖S‖ ≤ 1 := by
    change ‖U.val * T * (star U).val‖ ≤ 1
    rw [CStarRing.norm_mul_coe_unitary (U.val * T) (star U),
      CStarRing.norm_coe_unitary_mul U T, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1)).2
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases Real.sign_apply_eq (d i) with hi | hi | hi <;> norm_num [hi]
  calc
    _ ≤ ‖S‖ * traceNorm X :=
      D5.S3.Quantum.Matrix.UniformVarianceTraceBound.re_trace_mul_le S X
    _ ≤ traceNorm X := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hS (traceNorm_nonneg X)

open scoped Matrix.Norms.Frobenius

private theorem frobenius_sq_eq_trace_of_hermitian {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : ‖A‖ ^ 2 = (A * A).trace.re := by
  simpa only [Complex.ofReal_re, hA.eq] using
    congrArg Complex.re (frobenius_norm_sq_eq_trace A)

private theorem powers_stormer_of_roots (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖A - B‖ ^ 2 ≤ traceNorm (A * A - B * B) := by
  let D := A - B
  have hD : D.IsHermitian := hA.isHermitian.sub hB.isHermitian
  let U := hD.eigenvectorUnitary
  let d := hD.eigenvalues
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star U)
  let T : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sign (d i) : ℂ))
  let S := U.val * T * U.valᴴ
  let X := A * A - B * B
  have he (Y : Matrix n n ℂ) : e Y = U.valᴴ * Y * U.val := by
    simpa only [e, Matrix.star_eq_conjTranspose] using Unitary.conjStarAlgAut_star_apply U Y
  have htrace (Y : Matrix n n ℂ) : (e Y).trace = Y.trace := by
    rw [he Y, Matrix.trace_mul_cycle U.valᴴ Y U.val, ← Matrix.mul_assoc U.val U.valᴴ Y,
      show U.val * U.valᴴ = 1 from Matrix.mem_unitaryGroup_iff.mp U.prop, Matrix.one_mul]
  have hdiag : e D = Matrix.diagonal (fun i => (d i : ℂ)) := by
    simpa only [e, U, d, Function.comp_apply] using
      hD.conjStarAlgAut_star_eigenvectorUnitary
  have hnorm : ‖D‖ ^ 2 = ∑ i, d i ^ 2 := by
    calc
      ‖D‖ ^ 2 = (D * D).trace.re := frobenius_sq_eq_trace_of_hermitian hD
      _ = (e (D * D)).trace.re := congrArg Complex.re (htrace _).symm
      _ = ∑ i, d i ^ 2 := by
        rw [map_mul, hdiag, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, pow_two]
  have hX : e X =
      e A * Matrix.diagonal (fun i => (d i : ℂ)) +
        Matrix.diagonal (fun i => (d i : ℂ)) * e B := by
    have hsplit : X = A * D + D * B := by
      dsimp [X, D]
      noncomm_ring
    rw [hsplit, map_add, map_mul, map_mul, hdiag]
  have ha : (e A).PosSemidef := by
    rw [he]
    exact hA.conjTranspose_mul_mul_same U.val
  have hb : (e B).PosSemidef := by
    rw [he]
    exact hB.conjTranspose_mul_mul_same U.val
  have hdiff (i : n) : (e A i i).re - (e B i i).re = d i := by
    simpa only [D, map_sub, Matrix.sub_apply, Complex.sub_re, Matrix.diagonal_apply_eq,
      Complex.ofReal_re] using congrArg (fun Y : Matrix n n ℂ => (Y i i).re) hdiag
  have hpair : (S * X).trace = (T * e X).trace := by
    calc
      _ = (U.val * (T * (U.valᴴ * X))).trace := by simp only [S, Matrix.mul_assoc]
      _ = (T * (U.valᴴ * X) * U.val).trace := Matrix.trace_mul_comm _ _
      _ = _ := by rw [he X]; simp only [Matrix.mul_assoc]
  have hsum : (S * X).trace.re = ∑ i, |d i| * ((e A i i).re + (e B i i).re) := by
    rw [hpair, hX]
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, T, Matrix.mul_add,
      Matrix.diagonal_mul, Matrix.add_apply, Matrix.mul_diagonal, Complex.mul_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
    apply Finset.sum_congr rfl
    intro i _
    have hsign : Real.sign (d i) * d i = |d i| := by
      rcases lt_trichotomy (d i) 0 with hi | hi | hi
      · simp [Real.sign_of_neg hi, abs_of_neg hi]
      · simp [hi]
      · simp [Real.sign_of_pos hi, abs_of_pos hi]
    rw [← hsign]
    ring
  change ‖D‖ ^ 2 ≤ traceNorm X
  calc
    ‖D‖ ^ 2 = ∑ i, d i ^ 2 := hnorm
    _ ≤ ∑ i, |d i| * ((e A i i).re + (e B i i).re) := by
      apply Finset.sum_le_sum
      intro i _
      have hai : 0 ≤ (e A i i).re := (Complex.nonneg_iff.mp (ha.diag_nonneg (i := i))).1
      have hbi : 0 ≤ (e B i i).re := (Complex.nonneg_iff.mp (hb.diag_nonneg (i := i))).1
      have habs : |d i| ≤ (e A i i).re + (e B i i).re := by
        rw [← hdiff i, abs_le]
        constructor <;> linarith
      rw [← sq_abs (d i), pow_two]
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
    _ = (S * X).trace.re := hsum.symm
    _ ≤ traceNorm X := sign_test_le_traceNorm U d X

/-- The squared Frobenius distance of positive square roots is at most the
unhalved trace-norm distance of their positive semidefinite inputs. -/
theorem powers_stormer (α β : Matrix n n ℂ)
    (hα : α.PosSemidef) (hβ : β.PosSemidef) :
    ‖CFC.sqrt α - CFC.sqrt β‖ ^ 2 ≤ traceNorm (α - β) := by
  simpa only [CFC.sqrt_mul_sqrt_self α hα.nonneg, CFC.sqrt_mul_sqrt_self β hβ.nonneg] using
    powers_stormer_of_roots (CFC.sqrt α) (CFC.sqrt β)
      (CFC.sqrt_nonneg α).posSemidef (CFC.sqrt_nonneg β).posSemidef

/-- The centered sandwich on trace-one positive semidefinite matrices is
Hölder continuous in the unhalved trace norm with constant `2 * ‖L‖ₒₚ`. -/
theorem centered_sandwich_traceNorm_le (α β L : Matrix n n ℂ)
    (hα : α.PosSemidef) (hβ : β.PosSemidef)
    (htrα : α.trace = 1) (htrβ : β.trace = 1) (hL : L.IsHermitian) :
    traceNorm (CFC.sqrt α * L * CFC.sqrt α - CFC.sqrt β * L * CFC.sqrt β) ≤
      2 * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) L‖ * Real.sqrt (traceNorm (α - β)) := by
  let A := CFC.sqrt α
  let B := CFC.sqrt β
  let c := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) L‖
  have root_norm (ρ : Matrix n n ℂ) (hρ : ρ.PosSemidef) (htrρ : ρ.trace = 1) :
      ‖CFC.sqrt ρ‖ = 1 := by
    have h := frobenius_sq_eq_trace_of_hermitian (CFC.sqrt_nonneg ρ).posSemidef.isHermitian
    rw [CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, htrρ, Complex.one_re] at h
    nlinarith [norm_nonneg (CFC.sqrt ρ)]
  have hLA : ‖L * A‖ ≤ c := by
    simpa only [A, c, root_norm α hα htrα, mul_one] using frobenius_mul_le_op L A
  have hBL : ‖B * L‖ ≤ c := by
    have hB : Bᴴ = B := (CFC.sqrt_nonneg β).posSemidef.isHermitian.eq
    have h := Matrix.frobenius_norm_conjTranspose (B * L)
    rw [Matrix.conjTranspose_mul, hL.eq, hB] at h
    rw [← h]
    simpa only [B, c, root_norm β hβ htrβ, mul_one] using frobenius_mul_le_op L B
  have trace_product (Y Z : Matrix n n ℂ) : traceNorm (Y * Z) ≤ ‖Y‖ * ‖Z‖ := by
    simpa only [entryNormSq_eq_hs_sq, Real.sqrt_sq_eq_abs, abs_norm] using
      traceNorm_mul_le_hsSq Y Z
  have hroot : ‖A - B‖ ≤ Real.sqrt (traceNorm (α - β)) :=
    Real.le_sqrt_of_sq_le (powers_stormer α β hα hβ)
  change traceNorm (A * L * A - B * L * B) ≤ 2 * c * Real.sqrt (traceNorm (α - β))
  calc
    _ = traceNorm ((A - B) * (L * A) + (B * L) * (A - B)) := by
      congr 1
      noncomm_ring
    _ ≤ traceNorm ((A - B) * (L * A)) + traceNorm ((B * L) * (A - B)) :=
      traceNorm_add_le _ _
    _ ≤ ‖A - B‖ * ‖L * A‖ + ‖B * L‖ * ‖A - B‖ :=
      add_le_add (trace_product _ _) (trace_product _ _)
    _ ≤ ‖A - B‖ * c + c * ‖A - B‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hLA (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hBL (norm_nonneg _))
    _ = 2 * c * ‖A - B‖ := by ring
    _ ≤ 2 * c * Real.sqrt (traceNorm (α - β)) :=
      mul_le_mul_of_nonneg_left hroot (by dsimp [c]; positivity)

end D5.S3.Quantum.Foundation.PowersStormer
