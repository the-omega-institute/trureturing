/- GID: D5/S3/Constants/MoranComplexDimensions
   generality: G
   mirror-B: D5/B/S3/Constants/MoranComplexDimensions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For an equal-ratio self-similar set with M pieces at contraction φ^{-k}, the complexified Moran equation M·φ^{-k s}=1 holds at every complex dimension s_n = log M/(k log φ) + 2πi n/(k log φ), the log-periodic tower of solutions. -/

import Mathlib

namespace D5.S3.Constants.MoranComplexDimensions

open Complex

/-- The `n`-th complex dimension of an equal-ratio self-similar set with `M` pieces at
contraction ratio `φ^{-k}`: `s_n = D + 2πi n / (k log φ)` with `D = log M / (k log φ)`. -/
noncomputable def complexDimension (M k : ℕ) (φ : ℝ) (n : ℤ) : ℂ :=
  ((Real.log M / (k * Real.log φ) : ℝ) : ℂ) +
    ((2 * Real.pi * n) / (k * Real.log φ) : ℝ) * Complex.I

/-- The complexified Moran equation `M · φ^{-k s} = 1` holds at every complex dimension
`s_n`: the log-periodic tower of solutions to `Σ φ^{-k D} = 1` at equal ratio. -/
theorem moran_complex_dimension (M k : ℕ) (φ : ℝ)
    (hM : 0 < M) (hk : 0 < k) (hφ : 1 < φ) (n : ℤ) :
    (M : ℂ) * Complex.exp (-(k : ℂ) * complexDimension M k φ n * (Real.log φ : ℂ)) = 1 := by
  have hlogφ : Real.log φ ≠ 0 := ne_of_gt (Real.log_pos hφ)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hexp : -(k : ℂ) * complexDimension M k φ n * (Real.log φ : ℂ)
      = ((-(Real.log M) : ℝ) : ℂ) + ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold complexDimension
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hkR
    have hlogφC : (Real.log φ : ℂ) ≠ 0 := by exact_mod_cast hlogφ
    push_cast
    field_simp
    ring
  rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
     ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hMR]
  push_cast
  field_simp

end D5.S3.Constants.MoranComplexDimensions
