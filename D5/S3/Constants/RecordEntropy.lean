/- GID: D5/S3/Constants/RecordEntropy
   generality: G
   mirror-B: D5/B/S3/Constants/RecordEntropy
   mirror-E: none(waiver:exact-closed-integral-identities-only)
   anchors: []
   digest: Evaluate the binary record-entropy integral exactly. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Interval

namespace D5.S3.Constants.RecordEntropy

/-- The integral kernel for one summand of binary entropy has value one quarter. -/
theorem neg_mul_log_integral :
    ∫ u in (0 : ℝ)..1, (-u * Real.log u) = 1 / 4 := by
  let F : ℝ → ℝ := fun x => -((x * Real.log x) * x / 2 - x ^ 2 / 4)
  have hF_continuous : Continuous F := by
    dsimp [F]
    exact (((Real.continuous_mul_log.mul continuous_id).div_const 2).sub
      ((continuous_id.pow 2).div_const 4)).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := F) (by norm_num) _
    (by
      apply (Real.continuous_mul_log.neg.intervalIntegrable 0 1).congr
      intro u hu
      change -(u * Real.log u) = -u * Real.log u
      ring)
    (tendsto_nhdsWithin_of_tendsto_nhds hF_continuous.continuousAt.tendsto)
    (tendsto_nhdsWithin_of_tendsto_nhds hF_continuous.continuousAt.tendsto)]
  · norm_num [F]
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    dsimp [F]
    have hquarter : HasDerivAt (fun y : ℝ => y ^ 2 / 4) (x / 2) x := by
      convert ((hasDerivAt_id x).pow 2).div_const 4 using 1
      · rfl
      · rfl
      · funext y
        simp [Pi.pow_apply, id_eq]
      · simp [id_eq]
        ring
    convert ((Real.hasDerivAt_mul_log hx0).mul (hasDerivAt_id x)).div_const 2 |>.sub
      hquarter |>.neg using 1
    · funext y
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, id_eq]
    · simp only [id_eq]
      ring

/-- The uniform average of binary Shannon entropy, expressed in bits. -/
theorem haar_record_entropy_bits :
    ∫ u in (0 : ℝ)..1,
        (-u * Real.log u - (1 - u) * Real.log (1 - u)) / Real.log 2 =
      1 / (2 * Real.log 2) := by
  let f : ℝ → ℝ := fun u => -u * Real.log u
  have hf : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    apply (Real.continuous_mul_log.neg.intervalIntegrable 0 1).congr
    intro u hu
    change -(u * Real.log u) = -u * Real.log u
    ring
  have hf_comp : IntervalIntegrable (fun u => f (1 - u)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    convert Real.continuous_mul_log.neg.comp
      ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).sub continuous_id) using 1
    funext u
    simp only [Function.comp_apply, Pi.neg_apply, Pi.sub_apply, f, id_eq]
    ring
  have hsymm : ∫ u in (0 : ℝ)..1, f (1 - u) = 1 / 4 := by
    calc
      _ = ∫ u in (0 : ℝ)..1, f u := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left f 1 (a := (0 : ℝ)) (b := 1))
      _ = 1 / 4 := by simpa [f] using neg_mul_log_integral
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [intervalIntegral.integral_div]
  calc
    (∫ u in (0 : ℝ)..1,
        -u * Real.log u - (1 - u) * Real.log (1 - u)) / Real.log 2 =
        (∫ u in (0 : ℝ)..1, f u + f (1 - u)) / Real.log 2 := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _hu
      simp only [f]
      ring
    _ = ((∫ u in (0 : ℝ)..1, f u) + ∫ u in (0 : ℝ)..1, f (1 - u)) /
        Real.log 2 := by rw [intervalIntegral.integral_add hf hf_comp]
    _ = 1 / (2 * Real.log 2) := by
      rw [show (∫ u in (0 : ℝ)..1, f u) = 1 / 4 by
        simpa [f] using neg_mul_log_integral, hsymm]
      field_simp [hlog]
      ring

end D5.S3.Constants.RecordEntropy
