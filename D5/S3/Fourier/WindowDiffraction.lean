/- GID: D5/S3/Fourier/WindowDiffraction
   generality: G
   mirror-B: D5/B/S3/Fourier/WindowDiffraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Fourier coefficient of a finite interval window has the exact sine-kernel amplitude |sin(πm·length)|/(πm); for the golden window of length 1/φ this is the diffraction closed form |sin(πm/φ)|/(πm). -/

import Mathlib

namespace D5.S3.Fourier.WindowDiffraction

open scoped Interval

/-- The Fourier coefficient at positive mode `m` of the indicator of `[0, length]`
in the unit circle. -/
noncomputable def windowFourierCoefficient (length : ℝ) (m : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..length,
    Complex.exp ((-(2 * Real.pi * (m : ℝ)) * Complex.I) * x)

/-- The exact sine-kernel amplitude of a finite interval window. -/
theorem window_fourier_amplitude (length : ℝ) (m : ℕ) (hm : 0 < m) :
    ‖windowFourierCoefficient length m‖ =
      |Real.sin (Real.pi * (m : ℝ) * length)| / (Real.pi * (m : ℝ)) := by
  have hmReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpiM : 0 < Real.pi * (m : ℝ) := mul_pos Real.pi_pos hmReal
  let c : ℂ := -(2 * (Real.pi : ℂ) * (m : ℂ)) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (by exact_mod_cast (Nat.ne_of_gt hm))))
      Complex.I_ne_zero
  have harg : c * (length : ℂ) =
      Complex.I * ((-(2 * Real.pi * (m : ℝ)) * length : ℝ) : ℂ) := by
    dsimp [c]
    push_cast
    ring
  have hnormc : ‖c‖ = 2 * (Real.pi * (m : ℝ)) := by
    dsimp [c]
    rw [norm_mul, Complex.norm_I, mul_one, norm_neg, norm_mul, norm_mul]
    norm_num [abs_of_pos Real.pi_pos, abs_of_pos hmReal]
    ring
  rw [windowFourierCoefficient]
  change ‖∫ x in (0 : ℝ)..length, Complex.exp (c * x)‖ = _
  rw [integral_exp_mul_complex hc]
  rw [harg, norm_div]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [hnormc]
  rw [show (-(2 * Real.pi * (m : ℝ)) * length) / 2 =
      -(Real.pi * (m : ℝ) * length) by ring]
  rw [Real.sin_neg, Real.norm_eq_abs, abs_mul, abs_neg]
  norm_num
  field_simp

/-- The cut-and-project window of length `1 / phi` has the claimed diffraction amplitude. -/
theorem golden_window_fourier_amplitude (m : ℕ) (hm : 0 < m) :
    ‖windowFourierCoefficient (1 / ((1 + Real.sqrt 5) / 2)) m‖ =
      |Real.sin (Real.pi * (m : ℝ) / ((1 + Real.sqrt 5) / 2))| /
        (Real.pi * (m : ℝ)) := by
  simpa [div_eq_mul_inv, mul_assoc] using
    window_fourier_amplitude (1 / ((1 + Real.sqrt 5) / 2)) m hm

end D5.S3.Fourier.WindowDiffraction
