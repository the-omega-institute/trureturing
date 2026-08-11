/- GID: D5/S3/Constants/WignerYanaseSpectrum
   generality: G
   mirror-B: D5/B/S3/Constants/WignerYanaseSpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The five members of the Wigner–Yanase contraction spectrum, 1, 1/(2(1−ln2)), 2, 6/(11−12·ln2), 1/(1−ln2), are strictly increasing; the ordering follows from the elementary bounds on ln 2. -/

import Mathlib

namespace D5.S3.Constants.WignerYanaseSpectrum

open Real

/-- The five-member Wigner–Yanase contraction spectrum is strictly ordered:
`1 < 1/(2(1−ln2)) < 2 < 6/(11−12·ln2) < 1/(1−ln2)`. -/
theorem wy_contraction_spectrum_strict_order :
    (1 : ℝ) < 1 / (2 * (1 - Real.log 2)) ∧
    1 / (2 * (1 - Real.log 2)) < 2 ∧
    (2 : ℝ) < 6 / (11 - 12 * Real.log 2) ∧
    6 / (11 - 12 * Real.log 2) < 1 / (1 - Real.log 2) := by
  have hlo : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hhi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h1 : (0 : ℝ) < 1 - Real.log 2 := by linarith
  have h2 : (0 : ℝ) < 11 - 12 * Real.log 2 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith
  · rw [lt_div_iff₀ h2]; nlinarith
  · rw [div_lt_div_iff₀ h2 h1]; nlinarith

end D5.S3.Constants.WignerYanaseSpectrum
