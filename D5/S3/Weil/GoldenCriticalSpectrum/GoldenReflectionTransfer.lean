/- GID: D5/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer
   generality: I
   mirror-B: D5/B/S3/Weil/GoldenCriticalSpectrum/GoldenReflectionTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflection-paired golden gains are globally balanced, while pointwise neutrality occurs exactly at zero normal displacement. -/

import D5.S3.Weil.GoldenCriticalSpectrum.GoldenCriticalRadius

/-!
The determinant-like product of a reflected pair is always one. This paired
balance is weaker than pointwise neutrality. The latter is the exact radial
form of the critical-line condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.GoldenCriticalSpectrum.GoldenReflectionTransfer

open D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle

/-- One-shell gain of a normal displacement. -/
def goldenTransferGain (delta : ℝ) : ℝ :=
  Real.exp (goldenScalePeriod * delta)

/-- Every gain is positive. -/
theorem golden_transfer_gain_pos (delta : ℝ) :
    0 < goldenTransferGain delta := by
  unfold goldenTransferGain
  exact Real.exp_pos _

/-- Reflection in the normal coordinate takes gain to reciprocal gain. -/
theorem golden_transfer_gain_neg (delta : ℝ) :
    goldenTransferGain (-delta) = (goldenTransferGain delta)⁻¹ := by
  simp [goldenTransferGain, Real.exp_neg]

/-- A reflected pair is determinant-balanced for every displacement. -/
theorem reflected_transfer_product_one (delta : ℝ) :
    goldenTransferGain delta * goldenTransferGain (-delta) = 1 := by
  rw [golden_transfer_gain_neg]
  exact mul_inv_cancel₀ (ne_of_gt (golden_transfer_gain_pos delta))

/-- Pointwise unit gain is equivalent to zero normal displacement. -/
theorem golden_transfer_gain_eq_one_iff (delta : ℝ) :
    goldenTransferGain delta = 1 ↔ delta = 0 := by
  constructor
  · intro h
    have hExp :
        Real.exp (goldenScalePeriod * delta) = Real.exp 0 := by
      simpa [goldenTransferGain] using h
    have hArg := Real.exp_injective hExp
    exact (mul_eq_zero.mp hArg).resolve_left golden_scale_period_ne_zero
  · rintro rfl
    simp [goldenTransferGain]

/-- Both members of a reflected pair are pointwise neutral exactly when the
pair lies on the reflection-fixed axis. -/
theorem reflected_pair_pointwise_neutral_iff (delta : ℝ) :
    goldenTransferGain delta = 1 ∧ goldenTransferGain (-delta) = 1 ↔
      delta = 0 := by
  constructor
  · exact fun h => (golden_transfer_gain_eq_one_iff delta).1 h.1
  · rintro rfl
    simp [goldenTransferGain]

/-- Paired balance alone cannot force pointwise neutrality. -/
theorem paired_balance_strictly_weaker :
    (goldenTransferGain 1 * goldenTransferGain (-1) = 1) ∧
      goldenTransferGain 1 ≠ 1 := by
  constructor
  · exact reflected_transfer_product_one 1
  · exact (golden_transfer_gain_eq_one_iff 1).not.mpr (by norm_num)

#print axioms golden_transfer_gain_neg
#print axioms reflected_transfer_product_one
#print axioms golden_transfer_gain_eq_one_iff
#print axioms reflected_pair_pointwise_neutral_iff
#print axioms paired_balance_strictly_weaker

end D5.S3.Weil.GoldenCriticalSpectrum.GoldenReflectionTransfer
