/- GID: D5/S3/Constants/Transcription/C2Certificate
   generality: I
   mirror-B: D5/B/S3/Constants/Transcription/C2Certificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The registered second coefficient satisfies its transcription and error certificates. -/

import D5.S3.Constants.Values
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace D5.S3.Constants.Transcription.C2Certificate

open D5.S3.Constants.Values

private theorem sqrt_five_sq : (Real.sqrt 5) ^ 2 = 5 := by
  norm_num

private theorem sqrt_five_lower : (22360679 / 10000000 : ℝ) < Real.sqrt 5 := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

private theorem sqrt_five_upper : Real.sqrt 5 < (559017 / 250000 : ℝ) := by
  nlinarith [sqrt_five_sq, Real.sqrt_nonneg 5]

private theorem c2_error_certificate :
    |c2 - (9465 / 100000 : ℝ)| <= 15 / 100000 := by
  rw [abs_le]
  simp only [c2, bh, t0, t1]
  constructor <;> ring_nf <;> nlinarith [sqrt_five_lower, sqrt_five_upper]

private theorem corrected_t0_shift_within_error :
    |(3 - 7 * Real.sqrt 5 / 2) *
        ((27 - 13 * Real.sqrt 5) / 24 - t0)| <= (15 / 100000 : ℝ) := by
  rw [abs_le]
  simp only [t0]
  constructor <;> ring_nf <;>
    nlinarith [sqrt_five_sq, sqrt_five_lower, sqrt_five_upper]

private theorem log_candidate_lt :
    Real.log (4 / 3 : ℝ) / (2 * Real.pi) < 1 / 18 := by
  have hlog : Real.log (4 / 3 : ℝ) < 1 / 3 := by
    have h := Real.log_lt_sub_one_of_pos
      (x := (4 / 3 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  apply (div_lt_iff₀ (by positivity : 0 < (2 : ℝ) * Real.pi)).2
  nlinarith [Real.pi_gt_three]

private theorem kappa_eq_sqrt_sub_one_div_four :
    kappa = (Real.sqrt 5 - 1) / 4 := by
  rw [kappa, goldenRatio]
  field_simp
  nlinarith [sqrt_five_sq]

private theorem kappa_sq_gt : (19 / 200 : ℝ) < kappa ^ 2 := by
  rw [kappa_eq_sqrt_sub_one_div_four]
  nlinarith [sqrt_five_sq, sqrt_five_lower]

/-- The registered second coefficient obeys its exact transcription, its input and output error
certificates, the corrected-zero-moment stability check, and the four recorded candidate
exclusions. -/
theorem c2_transcription_certificate :
    c2 =
        (Real.sqrt 5 - 1) * bh / 2 +
          (3 - 7 * Real.sqrt 5 / 2) * t0 +
          3 * Real.sqrt 5 * t1 + (269 * Real.sqrt 5 - 623) / 48 ∧
      |c2 - (9465 / 100000 : ℝ)| <= 15 / 100000 ∧
      |t1 - (3182 / 100000 : ℝ)| <= 2 / 100000 ∧
      |bh - (-14076 / 100000 : ℝ)| <= 7 / 100000 ∧
      |(3 - 7 * Real.sqrt 5 / 2) *
          ((27 - 13 * Real.sqrt 5) / 24 - t0)| <= (15 / 100000 : ℝ) ∧
      c2 ≠ -2 / 63 ∧
      c2 ≠ Real.log (4 / 3) / (2 * Real.pi) ∧
      c2 ≠ 1 / 40 ∧
      c2 ≠ kappa ^ 2 := by
  have hc2_lower : (189 / 2000 : ℝ) <= c2 := by
    have h := c2_error_certificate
    rw [abs_le] at h
    nlinarith
  have hc2_upper : c2 <= (237 / 2500 : ℝ) := by
    have h := c2_error_certificate
    rw [abs_le] at h
    nlinarith
  refine ⟨rfl, c2_error_certificate, ?_, ?_, corrected_t0_shift_within_error, ?_, ?_, ?_, ?_⟩
  · norm_num [t1]
  · norm_num [bh]
  · intro h
    rw [h] at hc2_lower
    norm_num at hc2_lower
  · intro h
    rw [h] at hc2_lower
    nlinarith [log_candidate_lt]
  · intro h
    rw [h] at hc2_lower
    norm_num at hc2_lower
  · intro h
    rw [h] at hc2_upper
    nlinarith [kappa_sq_gt]

#print axioms c2_transcription_certificate

end D5.S3.Constants.Transcription.C2Certificate
