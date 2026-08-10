/- GID: D5/S3/Fourier/ReductionKernel
   generality: G
   mirror-B: D5/B/S3/Fourier/ReductionKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the cotangent reduction kernel and its golden-ratio specialization. -/

import Mathlib

namespace D5.S3.Fourier.ReductionKernel

/-- The fourth-harmonic cotangent kernel reduces to second- and fourth-harmonic
sine terms whenever the cotangent denominator is nonzero. -/
theorem reduction_kernel (x : ℝ) (hx : Real.sin x ≠ 0) :
    Real.cos (4 * x) * (Real.cos x / Real.sin x) =
      Real.cos x / Real.sin x - 2 * Real.sin (2 * x) - Real.sin (4 * x) := by
  have e4c : Real.cos (4 * x) =
      1 - 8 * Real.sin x ^ 2 * Real.cos x ^ 2 := by
    have h : (4 : ℝ) * x = 2 * (2 * x) := by ring
    rw [h, Real.cos_two_mul, Real.cos_two_mul]
    linear_combination (8 * Real.cos x ^ 2) * Real.sin_sq_add_cos_sq x
  have e4s : Real.sin (4 * x) =
      4 * Real.sin x * Real.cos x * (2 * Real.cos x ^ 2 - 1) := by
    have h : (4 : ℝ) * x = 2 * (2 * x) := by ring
    rw [h, Real.sin_two_mul, Real.sin_two_mul, Real.cos_two_mul]
    ring
  have e2s : Real.sin (2 * x) =
      2 * Real.sin x * Real.cos x := Real.sin_two_mul x
  rw [e4c, e4s, e2s]
  field_simp
  ring

/-- The reduction kernel at integer multiples of pi times the golden ratio. -/
theorem reduction_kernel_golden (k : ℕ)
    (hk : Real.sin (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) ≠ 0) :
    Real.cos (4 * Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) *
        (Real.cos (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) /
          Real.sin (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2))) =
      Real.cos (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) /
          Real.sin (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) -
        2 * Real.sin (2 * Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) -
        Real.sin (4 * Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) := by
  simpa [mul_assoc] using
    reduction_kernel
      (Real.pi * (k : ℝ) * ((1 + Real.sqrt 5) / 2)) hk

end D5.S3.Fourier.ReductionKernel
