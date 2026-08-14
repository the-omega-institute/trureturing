/- GID: D5/S3/Zeros/ToySpectrum/FourPointPowerDefect
   generality: G
   mirror-B: D5/B/S3/Zeros/ToySpectrum/FourPointPowerDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Four symmetric exponential points have a hyperbolic-trigonometric power defect. -/

/- Library-search audit trail (2026-08-14):
   * The exact four-point identity was not found in pinned Mathlib or D5.
   * `Complex.exp_nat_mul` converts powers of exponentials to scaled exponents.
   * `Complex.exp_add_mul_I` and `Real.cosh_eq` supply the polar and
     hyperbolic normal forms used below.
-/

import Mathlib.Analysis.Complex.Trigonometric

namespace D5.S3.Zeros.ToySpectrum.FourPointPowerDefect

/-- The sum of the power defects over the four exponential points with
independent sign choices on the radial and angular parameters. -/
noncomputable def fourPointPowerDefect (q theta : ℝ) (k : ℕ) : ℂ :=
  (1 - Complex.exp ((q : ℂ) + (theta : ℂ) * Complex.I) ^ k) +
    (1 - Complex.exp ((q : ℂ) + ((-theta : ℝ) : ℂ) * Complex.I) ^ k) +
    (1 - Complex.exp ((-q : ℝ) + (theta : ℂ) * Complex.I) ^ k) +
    (1 - Complex.exp ((-q : ℝ) + ((-theta : ℝ) : ℂ) * Complex.I) ^ k)

/-- Four symmetric exponential points have total power defect
`4 * (1 - cosh (kq) * cos (k theta))`. -/
theorem four_point_power_defect_eq (q theta : ℝ) (k : ℕ) :
    fourPointPowerDefect q theta k =
      (4 * (1 - Real.cosh (k * q) * Real.cos (k * theta)) : ℝ) := by
  have hexp (a b : ℝ) :
      Complex.exp ((a : ℂ) + (b : ℂ) * Complex.I) ^ k =
        (Real.exp (k * a) : ℂ) *
          ((Real.cos (k * b) : ℂ) + (Real.sin (k * b) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    rw [show (k : ℂ) * ((a : ℂ) + (b : ℂ) * Complex.I) =
        ((k * a : ℝ) : ℂ) + ((k * b : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    push_cast
    exact Complex.exp_add_mul_I (k * a) (k * b)
  unfold fourPointPowerDefect
  rw [hexp q theta, hexp q (-theta), hexp (-q) theta, hexp (-q) (-theta)]
  rw [Real.cosh_eq]
  push_cast
  rw [mul_neg, Complex.sin_neg, Complex.cos_neg]
  ring_nf

/-- The parameter domain is inhabited. -/
example : ℝ × ℝ × ℕ := (0, 0, 0)

/-- The assumption-free identity specializes at an explicit parameter triple. -/
example : fourPointPowerDefect 0 0 1 = 0 := by
  rw [four_point_power_defect_eq]
  norm_num

/- Replacing the constant term by two breaks the identity at an explicit input. -/
example :
    fourPointPowerDefect 0 0 1 ≠
      (4 * (2 - Real.cosh (1 * 0) * Real.cos (1 * 0)) : ℝ) := by
  rw [four_point_power_defect_eq]
  norm_num

#print axioms four_point_power_defect_eq

end D5.S3.Zeros.ToySpectrum.FourPointPowerDefect
