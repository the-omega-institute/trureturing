/- GID: D5/S3/Arith/Robin/ForwardKernel/Adjoint
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/Adjoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact adjoint transport preserves all Chebyshev atoms of the original forward kernel. -/

import D5.S3.Arith.Robin.ForwardKernel.Transport
import D5.S3.Arith.Robin.OriginalMovingCutAggregate
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The literal Mellin adjoint has compact center support and retains the signed price response. -/

namespace D5.S3.Arith.Robin.ForwardKernel.Adjoint

open Set MeasureTheory
open OriginalMovingWindowMoment (width endpoint kernel)
open ActualRobinClockCovariance (g)
open MellinWeightedVariation (weight)
open ActualVonMangoldtBandCompensation (weightedPrefix)
open ForwardKernel.Transport (forwardResponse)

noncomputable section

/-- The original price kernel transported against a compact interval of centers. -/
def compactAdjoint (a b : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x in Icc a b, f x * (kernel x t : ℂ)

/-- The Mellin adjoint of the original kernel over all legal centers. -/
def adjointKernel (x0 : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  ∫ x in Ici x0, (x : ℂ) ^ (-s - 1) * (kernel x t : ℂ)

/-- At each evaluation point the Mellin adjoint uses only a compact interval of centers. -/
lemma adjointKernel_eq_compact (x0 : ℝ) (s : ℂ) (t : ℝ) :
    adjointKernel x0 s t =
      compactAdjoint x0 (max x0 t) (fun x => (x : ℂ) ^ (-s - 1)) t := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici Icc_subset_Ici_self
  intro x hx
  have htx : t ≤ x := by
    have hmx : max x0 t < x := by
      exact lt_of_not_ge (fun h => hx.2 ⟨hx.1, h⟩)
    exact le_max_right x0 t |>.trans hmx.le
  simp [kernel, not_lt.mpr htx]

/-- The Mellin adjoint is an ordinary absolutely integrable integral at each point. -/
lemma adjointKernel_center_integrable {x0 : ℝ} (hx0 : 4 ≤ x0) (s : ℂ) (t : ℝ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (kernel x t : ℂ))
      (Ici x0) := by
  have hk : IntegrableOn (fun x => kernel x t) (Icc x0 (max x0 t)) :=
    OriginalMovingCutRow.kernel_integrableOn hx0
  have hc : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (kernel x t : ℂ))
      (Icc x0 (max x0 t)) := by
    apply hk.ofReal.continuousOn_mul _ isCompact_Icc
    apply Complex.continuous_ofReal.continuousOn.cpow_const
    intro x hx
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith [hx.1])
  apply hc.of_forall_sdiff_eq_zero measurableSet_Ici
  intro x hx
  have htx : t ≤ x := by
    have hmx : max x0 t < x := lt_of_not_ge (fun h => hx.2 ⟨hx.1, h⟩)
    exact le_max_right x0 t |>.trans hmx.le
  simp [kernel, not_lt.mpr htx]

private lemma normalization {x : ℝ} (hx : 1 < x) :
    Real.sqrt x / (weight x * width x ^ 2) =
      1 / (weight x * x ^ (11 / 10 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  have hw := OriginalMovingWindowMoment.weight_pos hx
  have hH : 0 < width x := Real.rpow_pos_of_pos hx0 _
  have hp := Real.rpow_pos_of_pos hx0 (11 / 10 : ℝ)
  have hs := OriginalMovingWindowMoment.width_scale hx0
  have he : width x ^ 2 = Real.sqrt x * x ^ (11 / 10 : ℝ) := by
    exact (div_eq_iff hp.ne').mp (hs.trans (Real.sqrt_eq_rpow x).symm)
  field_simp [hw.ne', hH.ne', hp.ne']
  nlinarith

private lemma kernel_integral {x : ℝ} (hx : 1 < x) :
    (∫ t in x..endpoint x, kernel x t) =
      (∫ t in x..endpoint x, g t - g (endpoint x)) /
        (weight x * x ^ (11 / 10 : ℝ)) := by
  have hxb : x ≤ endpoint x := by
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)
  rw [← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  rw [uIoc_of_le hxb] at ht
  exact if_pos ht

lemma forwardResponse_eq_prefix_kernel {x : ℝ} (hx : 1 < x) :
    forwardResponse x = weightedPrefix (kernel x) (endpoint x) -
      ∫ t in x..endpoint x, kernel x t := by
  have hx0 : 0 < x := by linarith
  have hxb : x ≤ endpoint x := by
    exact le_add_of_nonneg_right (Real.rpow_nonneg hx0.le _)
  have hsupport := ActualVonMangoldtBandCompensation.supported_prefix
    (f := fun t => (g t - g (endpoint x)) / (weight x * x ^ (11 / 10 : ℝ)))
    (r := kernel x) hx0.le (hx0.trans_le hxb) hxb
    (fun _ => rfl)
  simp only [weightedPrefix, QuotientIntegralBudget.arithmeticPrefix] at hsupport
  simp_rw [← mul_div_assoc, ← Finset.sum_div] at hsupport
  change weightedPrefix (kernel x) (endpoint x) =
    weightedPrefix (fun t => g t - g (endpoint x)) (endpoint x) /
      (weight x * x ^ (11 / 10 : ℝ)) -
    weightedPrefix (fun t => g t - g (endpoint x)) x /
      (weight x * x ^ (11 / 10 : ℝ)) at hsupport
  rw [ForwardKernel.Transport.forwardResponse_eq_signed_price hx, normalization hx,
    kernel_integral hx]
  change _ = _
  rw [hsupport]
  ring

#print axioms adjointKernel_center_integrable
#print axioms forwardResponse_eq_prefix_kernel

end

end D5.S3.Arith.Robin.ForwardKernel.Adjoint
