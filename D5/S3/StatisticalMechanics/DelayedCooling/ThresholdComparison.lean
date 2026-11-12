/- GID: D5/S3/StatisticalMechanics/DelayedCooling/ThresholdComparison
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/DelayedCooling/ThresholdComparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Threshold comparison for signed controls of the concrete delay kernel. -/

module

public import D5.S3.StatisticalMechanics.DelayedCooling.ShiftOrder
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Threshold comparison under the concrete source kernel

The result concerns integrable signed controls. Identifying every source bath
history with such a control and its sample with this convolution is a separate
obligation; the theorem imposes no history-class definition.
-/

public section

namespace D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison

open Set MeasureTheory
open Kernel ShiftOrder

noncomputable section

/-- The analytic two-reservoir contrast, before optimizing the waiting time. -/
@[expose] def synchronousDifference (τ w t : ℝ) : ℝ :=
  2 * relaxation τ (t + w) - relaxation τ t

private def thresholdControl (w a : ℝ) : ℝ := if w < a then 1 else -1

private theorem threshold_convolution {τ t w : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    IntegrableOn (fun a => responseKernel τ (t + a) * thresholdControl w a) (Ioi 0) ∧
      (∫ a in Ioi 0, responseKernel τ (t + a) * thresholdControl w a) =
        synchronousDifference τ w t := by
  have hi := (kernel_tail_mass hτ hsmall (t := t) (L := 0) (by simpa using ht)).1
  have hiw := Integrable.indicator hi (s := Ioi w) measurableSet_Ioi
  have heq : (fun a => responseKernel τ (t + a) * thresholdControl w a) =
      (fun a => 2 * (Ioi w).indicator (fun a => responseKernel τ (t + a)) a -
        responseKernel τ (t + a)) := by
    funext a
    by_cases ha : w < a <;> simp [thresholdControl, ha, two_mul]
  rw [heq]
  refine ⟨(hiw.const_mul 2).sub hi, ?_⟩
  rw [integral_sub (hiw.const_mul 2) hi, integral_const_mul,
    setIntegral_indicator measurableSet_Ioi]
  have hinter : Ioi (0 : ℝ) ∩ Ioi w = Ioi w :=
    inter_eq_self_of_subset_right (fun _ ha => lt_of_le_of_lt hw ha)
  rw [hinter, (kernel_tail_mass hτ hsmall (show 0 ≤ t + w by linarith)).2,
    (kernel_tail_mass hτ hsmall (t := t) (L := 0) (by simpa using ht)).2]
  simp [synchronousDifference]

/-- Among bounded signed controls with at least the threshold control's initial
weighted moment, that threshold control minimizes every future weighted moment.
All integrability premises are explicit and must be supplied by a history bridge. -/
theorem threshold_comparison {τ t w : ℝ} (hτ : 0 < τ)
    (hsmall : τ ≤ Real.exp (-1)) (ht : 0 ≤ t) (hw : 0 ≤ w) (u : ℝ → ℝ)
    (hi0 : IntegrableOn (fun a => responseKernel τ a * u a) (Ioi 0))
    (hit : IntegrableOn (fun a => responseKernel τ (t + a) * u a) (Ioi 0))
    (hu : ∀ a ∈ Ioi (0 : ℝ), -1 ≤ u a ∧ u a ≤ 1)
    (hgap : synchronousDifference τ w 0 ≤ ∫ a in Ioi 0, responseKernel τ a * u a) :
    synchronousDifference τ w t ≤ ∫ a in Ioi 0, responseKernel τ (t + a) * u a := by
  let cutRatio := responseKernel τ (t + w) / responseKernel τ w
  have hkw : 0 < responseKernel τ w := by
    simpa [responseKernel] using! relaxation_pos hτ hsmall (w - τ)
  have hktw : 0 < responseKernel τ (t + w) := by
    simpa [responseKernel] using! relaxation_pos hτ hsmall (t + w - τ)
  have hcutRatio : 0 < cutRatio := div_pos hktw hkw
  have hv0 := threshold_convolution hτ hsmall (t := 0) le_rfl hw
  simp only [zero_add] at hv0
  have hvt := threshold_convolution hτ hsmall ht hw
  have hp : ∀ a ∈ Ioi (0 : ℝ),
      responseKernel τ (t + a) * thresholdControl w a + cutRatio * (responseKernel τ a * u a) ≤
        responseKernel τ (t + a) * u a +
          cutRatio * (responseKernel τ a * thresholdControl w a) := by
    intro a ha
    have hub := hu a ha
    by_cases hwa : w < a
    · have horder := kernel_shift_order hτ hsmall hwa.le ht
      have hratio : responseKernel τ (t + a) ≤ cutRatio * responseKernel τ a := by
        dsimp [cutRatio]
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀ hkw).mpr horder
      have hh := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hratio)
        (sub_nonpos.mpr hub.2)
      simp only [thresholdControl, ite_eq_left hwa]
      nlinarith
    · have haw : a ≤ w := le_of_not_gt hwa
      have horder := kernel_shift_order hτ hsmall haw ht
      have hratio : cutRatio * responseKernel τ a ≤ responseKernel τ (t + a) := by
        dsimp [cutRatio]
        rw [div_mul_eq_mul_div]
        exact (div_le_iff₀ hkw).mpr horder
      have hh := mul_nonneg (sub_nonneg.mpr hratio) (by linarith : 0 ≤ u a + 1)
      simp only [thresholdControl, ite_eq_right hwa]
      nlinarith
  have hm := integral_mono_ae (hvt.1.add (hi0.const_mul cutRatio))
    (hit.add (hv0.1.const_mul cutRatio)) (ae_restrict_of_forall_mem measurableSet_Ioi hp)
  simp only [Pi.add_apply] at hm
  rw [integral_add hvt.1 (hi0.const_mul cutRatio), integral_add hit (hv0.1.const_mul cutRatio),
    integral_const_mul, integral_const_mul, hvt.2, hv0.2] at hm
  nlinarith [mul_nonneg hcutRatio.le (sub_nonneg.mpr hgap)]

end

end D5.S3.StatisticalMechanics.DelayedCooling.ThresholdComparison
