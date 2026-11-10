/- GID: D5/S3/Arith/Robin/ForwardKernel/Transport
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/Transport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete Chebyshev forward response equals its finite signed price-kernel sum. -/

import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import D5.S3.Arith.Robin.ActualVonMangoldtBandCompensation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The finite price identity retains all prime powers in the original forward response. -/

namespace D5.S3.Arith.Robin.ForwardKernel.Transport

open Set MeasureTheory
open OriginalMovingWindowMoment (width endpoint weight_continuous)
open MellinWeightedVariation (weight)
open ActualRobinClockCovariance (g)
open ActualVonMangoldtBandCompensation (discrepancy weightedPrefix)

noncomputable section

/-- The normalized response of the original forward window to the complete Chebyshev error. -/
def forwardResponse (x : ℝ) : ℝ :=
  Real.sqrt x / width x ^ 2 *
    ∫ u in (0 : ℝ)..width x,
      (discrepancy (x + u) - discrepancy x) * (weight (x + u) / weight x)

private lemma weighted_error_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (discrepancy t - discrepancy a) * weight t)
      volume a b := by
  have he : IntervalIntegrable discrepancy volume a b :=
    Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable _ _)
  apply (he.sub intervalIntegrable_const).mul_continuousOn
  rw [uIcc_of_le hab]
  exact weight_continuous ha

/-- The integral defining the original response exists at every center above one. -/
lemma forwardResponse_intervalIntegrable {x : ℝ} (hx : 1 < x) :
    IntervalIntegrable
      (fun u => (discrepancy (x + u) - discrepancy x) * (weight (x + u) / weight x))
      volume 0 (width x) := by
  have hwidth : 0 ≤ width x := Real.rpow_nonneg (by linarith) _
  have he := (weighted_error_integrable hx (le_add_of_nonneg_right hwidth)).comp_add_left x
  simpa only [sub_self, add_sub_cancel_left, mul_div_assoc] using he.div_const (weight x)

/-- Exact QG7 transport. The difference of right-closed arithmetic prefixes
excludes every atom at the initial endpoint; the terminal price difference is zero. -/
theorem forwardResponse_eq_signed_price {x : ℝ} (hx : 1 < x) :
    forwardResponse x = Real.sqrt x / (weight x * width x ^ 2) *
      (weightedPrefix (fun t => g t - g (endpoint x)) (endpoint x) -
        weightedPrefix (fun t => g t - g (endpoint x)) x -
        ∫ t in x..endpoint x, g t - g (endpoint x)) := by
  have hx0 : 0 < x := by linarith
  have hwidth : 0 ≤ width x := Real.rpow_nonneg hx0.le _
  have hxb : x ≤ endpoint x := le_add_of_nonneg_right hwidth
  have hz : ∀ t ∈ Icc x (endpoint x), 0 < Real.log (t / 1) := by
    intro t ht
    simpa only [div_one] using Real.log_pos (hx.trans_le ht.1)
  have harith := ActualVonMangoldtBandCompensation.band_mass_forward
    (c := 1) (by norm_num) hx0 hxb hz
  have hvolume := ActualVonMangoldtBandCompensation.triangle_volume_forward
    (c := 1) (by norm_num) hx0 hxb hz
  simp only [ActualVonMangoldtBandCompensation.reciprocalLog,
    ActualVonMangoldtBandCompensation.bandDerivative, div_one] at harith hvolume
  change weightedPrefix (fun t => g t - g (endpoint x)) (endpoint x) -
    weightedPrefix (fun t => g t - g (endpoint x)) x =
      ∫ t in x..endpoint x, weight t * (Chebyshev.psi t - Chebyshev.psi x) at harith
  change (∫ t in x..endpoint x, g t - g (endpoint x)) =
    ∫ t in x..endpoint x, weight t * (t - x) at hvolume
  have hpsi : IntervalIntegrable
      (fun t => weight t * (Chebyshev.psi t - Chebyshev.psi x)) volume x (endpoint x) := by
    apply (Chebyshev.psi_mono.intervalIntegrable.sub intervalIntegrable_const).continuousOn_mul
    rw [uIcc_of_le hxb]
    exact weight_continuous hx
  have hid : IntervalIntegrable (fun t => weight t * (t - x)) volume x (endpoint x) := by
    apply ((continuous_id.sub continuous_const).intervalIntegrable x (endpoint x)).continuousOn_mul
    rw [uIcc_of_le hxb]
    exact weight_continuous hx
  have herror : (∫ t in x..endpoint x, (discrepancy t - discrepancy x) * weight t) =
      weightedPrefix (fun t => g t - g (endpoint x)) (endpoint x) -
        weightedPrefix (fun t => g t - g (endpoint x)) x -
        ∫ t in x..endpoint x, g t - g (endpoint x) := by
    rw [harith, hvolume, ← intervalIntegral.integral_sub hpsi hid]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [discrepancy]
    ring
  have hshift := intervalIntegral.integral_comp_add_left
    (f := fun t => (discrepancy t - discrepancy x) * weight t)
    (a := 0) (b := width x) x
  simp only [add_zero] at hshift
  change (∫ u in (0 : ℝ)..width x, (discrepancy (x + u) - discrepancy x) * weight (x + u)) =
    ∫ t in x..endpoint x, (discrepancy t - discrepancy x) * weight t at hshift
  unfold forwardResponse
  simp_rw [← mul_div_assoc]
  rw [intervalIntegral.integral_div, hshift, herror]
  ring

#print axioms forwardResponse_eq_signed_price

end

end D5.S3.Arith.Robin.ForwardKernel.Transport
