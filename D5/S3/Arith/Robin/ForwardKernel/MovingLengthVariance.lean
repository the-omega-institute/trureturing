/- GID: D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/MovingLengthVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The variance band bounds all increments in the moving-length strip. -/

import D5.S3.Arith.Robin.ForwardKernel.FixedLengthCovariance

/-! A uniform variance estimate for all lengths between X^(4/5) and 4 X^(4/5). -/

namespace D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance

open Set MeasureTheory Filter
open scoped Topology
open VarianceTransferDefs VarianceTransfer

noncomputable section

/-- The variance band gives one logarithm uniformly over the moving-length strip. -/
theorem moving_strip_variance_bound {E : ℝ → ℝ} (hE : LocallyBoundedMeasurable E)
    (hGM : CumulativeVarianceBandAsymptoticFor E) :
    ∀ᶠ X : ℝ in atTop, ∀ u ∈ Icc (X ^ (4 / 5 : ℝ)) (4 * X ^ (4 / 5 : ℝ)),
      (∫ x in X..(2 * X), increment E u x ^ 2) ≤
        32 * X * X ^ (4 / 5 : ℝ) * Real.log X := by
  have hY : Tendsto (fun X : ℝ => 2 * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hlo := FixedLengthCovariance.shifted_band
    (c := 1) (d := 2) (q := 1) (r := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hhi := FixedLengthCovariance.shifted_band
    (c := 1) (d := 2) (q := 4) (r := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlo, hhi,
    hY.eventually (hGM 1 zero_lt_one)] with X hX hlo hhi hV
  have hband : (2 * X) ^ (3 / 4 : ℝ) ≤ X ^ (4 / 5 : ℝ) ∧
      4 * X ^ (4 / 5 : ℝ) ≤ (2 * X) ^ (7 / 8 : ℝ) := by
    simpa only [fixedLength, one_mul, zero_mul, add_zero] using And.intro hlo.1 hhi.2
  intro u hu
  have hX0 : 0 < X := by linarith
  have hY1 : 1 < 2 * X := by linarith
  have hH0 : 0 < X ^ (4 / 5 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hu0 : 0 < u := hH0.trans_le hu.1
  have hu1 : 1 ≤ u := (Real.one_le_rpow (by linarith : 1 ≤ X)
    (by norm_num : (0 : ℝ) ≤ 4 / 5)).trans hu.1
  have huY : u < 2 * X := by
    calc
      _ ≤ (2 * X) ^ (7 / 8 : ℝ) := hu.2.trans hband.2
      _ < (2 * X) ^ (1 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hY1 (by norm_num)
      _ = _ := Real.rpow_one _
  have hlogpos : 0 < Real.log (2 * X / u) :=
    Real.log_pos ((one_lt_div hu0).mpr huY)
  have hlog : Real.log (2 * X / u) ≤ 2 * Real.log X := by
    have hle : 2 * X / u ≤ 2 * X := div_le_self (by positivity) hu1
    have ht := Real.log_le_log (div_pos (by positivity) hu0) hle
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX0.ne'] at ht
    have hl2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    linarith
  have hv := (abs_sub_le_iff.mp (hV u (hband.1.trans hu.1) (hu.2.trans hband.2))).1
  have hden : 0 < (2 * X) * u * Real.log (2 * X / u) := by positivity
  have hv' : cumulativeVariance E (2 * X) u ≤
      2 * ((2 * X) * u * Real.log (2 * X / u)) := by
    apply (div_le_iff₀ hden).mp
    linarith
  have hi : IntervalIntegrable (fun x => increment E u x ^ 2) volume 1 (2 * X) := by
    simpa only [pow_two, Pi.mul_apply, id_eq] using
      (increment_product_comp_integrableOn hE isCompact_uIcc
        continuous_const continuous_id continuous_const continuous_id).intervalIntegrable
  have hsub : (∫ x in X..(2 * X), increment E u x ^ 2) ≤
      cumulativeVariance E (2 * X) u := by
    exact intervalIntegral.integral_mono_interval (by linarith : 1 ≤ X)
      (by linarith : X ≤ 2 * X) le_rfl (Eventually.of_forall (fun _ => sq_nonneg _)) hi
  calc
    _ ≤ 2 * ((2 * X) * u * Real.log (2 * X / u)) := hsub.trans hv'
    _ ≤ 2 * ((2 * X) * (4 * X ^ (4 / 5 : ℝ)) * (2 * Real.log X)) := by
      gcongr
      exact hu.2
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.MovingLengthVariance
