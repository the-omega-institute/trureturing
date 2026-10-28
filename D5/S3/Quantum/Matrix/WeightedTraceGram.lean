/- GID: D5/S3/Quantum/Matrix/WeightedTraceGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/WeightedTraceGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Positive weighted trace Gram forms in arbitrary finite complex dimension. -/

/-
admission_basis: escape-witness
proof_shape: weighted_traceGram_nonneg: content
escape_witness: weighted_traceGram_nonneg
The two physical matrix weights and the coefficient Gram matrix are independent.
No invertibility, commutativity, or fixed physical dimension is assumed.
-/

module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import D5.S3.Quantum.Matrix.HsfQubitMixedCubic

/-! Weighted Gram positivity with independent positive matrix weights.
Source-selection evidence for the escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/23332. -/

@[expose] public section
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.WeightedTraceGram
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The order of the four matrix factors is part of this definition. -/
def traceGram (L R : Matrix n n ℂ) (q : m → Matrix n n ℂ)
    (M : Matrix m m ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * (Matrix.trace (L * star (q i) * R * q j)).re

private theorem square_nonneg (L R S : Matrix n n ℂ)
    (hL : L.PosSemidef) (hR : R.PosSemidef) :
    0 ≤ (Matrix.trace (L * star S * R * S)).re := by
  simpa only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose, RCLike.re_to_complex] using
    HsfQubitMixedCubic.trace_mul_nonneg_of_posSemidef hL
      (hR.conjTranspose_mul_mul_same S)

private theorem rankOne_identity (L R : Matrix n n ℂ) (q : m → Matrix n n ℂ)
    (v : m → ℝ) :
    traceGram L R q (Matrix.of fun i j => v i * v j) =
      (Matrix.trace (L * star (∑ i, v i • q i) * R * (∑ j, v j • q j))).re := by
  have re_sum (f : m → ℂ) : (∑ i, f i).re = ∑ i, (f i).re :=
    map_sum Complex.reCLM f Finset.univ
  simp only [traceGram, star_sum, star_smul, star_trivial,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, re_sum, Complex.real_smul,
    Finset.mul_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Real positive semidefinite coefficient matrices give positive weighted trace forms.
Both PSD physical weights may be singular, and the words need not be Hermitian. -/
theorem weighted_traceGram_nonneg (L R : Matrix n n ℂ) (q : m → Matrix n n ℂ)
    (M : Matrix m m ℝ) (hL : L.PosSemidef) (hR : R.PosSemidef)
    (hM : M.PosSemidef) : 0 ≤ traceGram L R q M := by
  let V := CFC.sqrt M
  have hV : star V * V = M := by
    rw [(CFC.sqrt_nonneg M).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self M hM.nonneg
  have he : M = ∑ k, (Matrix.of fun i j => V k i * V k j) := by
    rw [← hV]
    ext i j
    simp [Matrix.mul_apply, Matrix.star_apply, Matrix.sum_apply]
  have hs : traceGram L R q (∑ k, Matrix.of fun i j => V k i * V k j) =
      ∑ k, traceGram L R q (Matrix.of fun i j => V k i * V k j) := by
    simp only [traceGram, Matrix.sum_apply, Matrix.of_apply, Finset.sum_mul]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    exact Finset.sum_comm
  rw [he, hs]
  apply Finset.sum_nonneg
  intro k hk
  rw [rankOne_identity]
  exact square_nonneg L R _ hL hR

end D5.S3.Quantum.Matrix.WeightedTraceGram
