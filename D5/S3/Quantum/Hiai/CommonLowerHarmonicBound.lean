/- GID: D5/S3/Quantum/Hiai/CommonLowerHarmonicBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/CommonLowerHarmonicBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular common positive lower bounds are dominated by the matrix harmonic mean. -/

import D5.S3.Quantum.Hiai.ParallelSumVariational
import Mathlib.Tactic.Module

noncomputable section
namespace D5.S3.Quantum.Hiai.CommonLowerHarmonicBound
open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Hiai.ParallelSumVariational
variable {d : Type*} [Fintype d] [DecidableEq d]

private lemma split_energy_mono {P Q K : Matrix d d ℂ}
    (hKP : K ≤ P) (hKQ : K ≤ Q) (W : Matrix d d ℂ × Matrix d d ℂ) :
    splitEnergy K K W ≤ splitEnergy P Q W := by
  have hu : W.1ᴴ * K * W.1 ≤ W.1ᴴ * P * W.1 := by
    apply Matrix.le_iff.mpr
    convert (Matrix.le_iff.mp hKP).conjTranspose_mul_mul_same W.1 using 1
    simp only [mul_sub, sub_mul]
  have hv : W.2ᴴ * K * W.2 ≤ W.2ᴴ * Q * W.2 := by
    apply Matrix.le_iff.mpr
    convert (Matrix.le_iff.mp hKQ).conjTranspose_mul_mul_same W.2 using 1
    simp only [mul_sub, sub_mul]
  exact add_le_add hu hv

private lemma split_energy_common_floor {K U V : Matrix d d ℂ}
    (hK : K.PosSemidef) (hUV : U + V = 1) :
    K ≤ (2 : ℝ) • (Uᴴ * K * U + Vᴴ * K * V) := by
  have he : (U + V)ᴴ * K * (U + V) = K := by rw [hUV]; simp
  apply Matrix.le_iff.mpr
  convert hK.conjTranspose_mul_mul_same (U - V) using 1
  calc
    (2 : ℝ) • (Uᴴ * K * U + Vᴴ * K * V) - K =
        (2 : ℝ) • (Uᴴ * K * U + Vᴴ * K * V) - (U + V)ᴴ * K * (U + V) := by rw [he]
    _ = (U - V)ᴴ * K * (U - V) := by
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, add_mul, mul_add, sub_mul, mul_sub]
      module

/-- Any complex split of the identity gives an upper bound for a common PSD lower matrix.
The inputs themselves may be singular. -/
theorem common_lower_split_bound {P Q K : Matrix d d ℂ}
    (hK : K.PosSemidef) (hKP : K ≤ P) (hKQ : K ≤ Q)
    (W : Matrix d d ℂ × Matrix d d ℂ) (hW : W.1 + W.2 = 1) :
    K ≤ (2 : ℝ) • splitEnergy P Q W := by
  exact (split_energy_common_floor hK hW).trans
    (smul_le_smul_of_nonneg_left (split_energy_mono hKP hKQ W) (by norm_num))

/-- The common lower matrix may be singular and need not commute with either input.
The proof uses the attained quadratic minimum and never inverts the lower matrix. -/
theorem common_lower_harmonic_bound {P Q K : Matrix d d ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) (hK : K.PosSemidef)
    (hKP : K ≤ P) (hKQ : K ≤ Q) :
    K ≤ (2 : ℝ) • parallelSum P Q ∧
      K.trace.re ≤ 2 * (parallelSum P Q).trace.re := by
  obtain ⟨W, _, _, hW, hE, _⟩ := parallel_sum_minimum hP hQ (1 : Matrix d d ℂ)
  simp only [Matrix.conjTranspose_one, one_mul, mul_one] at hE
  have hbound : K ≤ (2 : ℝ) • parallelSum P Q := by
    simpa only [hE] using common_lower_split_bound hK hKP hKQ W hW
  refine ⟨hbound, ?_⟩
  have ht := (Matrix.le_iff.mp hbound).trace_nonneg
  have hr := (Complex.nonneg_iff.mp ht).1
  simpa only [Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re,
    smul_eq_mul, sub_nonneg] using hr

#print axioms common_lower_harmonic_bound
end D5.S3.Quantum.Hiai.CommonLowerHarmonicBound
