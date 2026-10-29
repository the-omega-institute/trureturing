/- GID: D5/S3/Arith/Robin/ForwardKernel/InverseTransport
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/InverseTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The literal forward Mellin adjoint equals its inverse-coordinate integral. -/

import D5.S3.Arith.Robin.ForwardKernel.Adjoint
import D5.S3.Arith.Robin.ForwardKernel.Remainder
import D5.S3.Arith.Robin.ForwardKernel.WeightControl
import D5.S3.Arith.Robin.ForwardKernel.Asymptotic
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! The finite forward price kernel admits the inverse coordinates of the moving window. -/

namespace D5.S3.Arith.Robin.ForwardKernel.InverseTransport

open Set MeasureTheory
open OriginalMovingWindowMoment (width endpoint kernel)
open ActualRobinClockCovariance (g)
open MellinWeightedVariation (weight)
open ForwardKernel.Remainder (coordinate)
open ForwardKernel.WeightControl (weightRatio)
open ForwardKernel.Adjoint (adjointKernel)

noncomputable section

private lemma price_ratio_integral {x z : ℝ} (hx : 1 < x) (hz : z ∈ Icc (0 : ℝ) 1) :
    g (x + z * width x) - g (endpoint x) =
      width x * weight x * ∫ u in z..1, weightRatio x u := by
  have hx0 : 0 < x := by linarith
  have hH : 0 < width x := Real.rpow_pos_of_pos hx0 _
  have hw := OriginalMovingWindowMoment.weight_pos hx
  have hs : 1 < x + width x * z := by nlinarith [hz.1]
  have horder : x + width x * z ≤ x + width x := by nlinarith [hz.2]
  have hscale := intervalIntegral.smul_integral_comp_add_mul
    (f := weight) (a := z) (b := 1) (width x) x
  simp only [smul_eq_mul, mul_one] at hscale
  have hdensity := ActualRobinClockCovariance.density_integral hs horder
  change (∫ t in (x + width x * z)..(x + width x), weight t) =
    g (x + width x * z) - g (x + width x) at hdensity
  rw [hdensity] at hscale
  have hr : (∫ u in z..1, weightRatio x u) =
      (∫ u in z..1, weight (x + width x * u)) / weight x := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [weightRatio, mul_comm u (width x)]
  rw [hr]
  dsimp [endpoint]
  rw [mul_comm z (width x)]
  field_simp [hw.ne']
  nlinarith [hscale]

private lemma transformed_integrand {t z : ℝ} (ht : 8 ≤ t)
    (hz : z ∈ Ioo (0 : ℝ) 1) (s : ℂ) :
    ((width (coordinate t z) /
      (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)) : ℝ) : ℂ) *
        ((coordinate t z : ℂ) ^ (-s - 1) * (kernel (coordinate t z) t : ℂ)) =
      (coordinate t z : ℂ) ^ (-s - 1 / 2) *
        ((∫ u in z..1, weightRatio (coordinate t z) u) : ℂ) /
          (((1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)) : ℝ) : ℂ) := by
  let x := coordinate t z
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := ForwardKernel.Remainder.coordinate_pos ht0 hz.1.le
  have hx4 : 4 ≤ x := by
    have h := ForwardKernel.Remainder.coordinate_half (by linarith : 2 ≤ t)
      (show z ∈ Icc (0 : ℝ) 1 from ⟨hz.1.le, hz.2.le⟩)
    dsimp [x]
    linarith
  have hH : 0 < width x := Real.rpow_pos_of_pos hx0 _
  have hw := OriginalMovingWindowMoment.weight_pos (show 1 < x by linarith)
  have hz0 : 0 ≤ z := hz.1.le
  have hD : 0 < 1 + (4 / 5 : ℝ) * z * x ^ (-1 / 5 : ℝ) := by positivity
  have hp : 0 < x ^ (11 / 10 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have he := ForwardKernel.Remainder.coordinate_equation ht0 hz.1.le
  change t = x + z * width x at he
  have hxt : x < t := by nlinarith [mul_pos hz.1 hH]
  have htB : t ≤ endpoint x := by dsimp [endpoint]; nlinarith [hz.2]
  have hprice := price_ratio_integral (show 1 < x by linarith)
    (show z ∈ Icc (0 : ℝ) 1 from ⟨hz.1.le, hz.2.le⟩)
  rw [← he] at hprice
  change ((width x / (1 + (4 / 5 : ℝ) * z * x ^ (-1 / 5 : ℝ)) : ℝ) : ℂ) *
      ((x : ℂ) ^ (-s - 1) * (kernel x t : ℂ)) = _
  rw [kernel, if_pos ⟨hxt, htB⟩, hprice]
  have hpower : (x : ℂ) ^ (-s - 1) * (Real.sqrt x : ℂ) = (x : ℂ) ^ (-s - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx0.le]
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx0.ne')]
    congr 1
    ring
  calc
    _ = (x : ℂ) ^ (-s - 1) *
        (((width x ^ 2 / x ^ (11 / 10 : ℝ)) : ℝ) : ℂ) *
        ((∫ u in z..1, weightRatio x u) : ℂ) /
          (((1 + (4 / 5 : ℝ) * z * x ^ (-1 / 5 : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rw [intervalIntegral.integral_ofReal]
      field_simp [hw.ne', hp.ne', hD.ne']
      <;> ring
    _ = _ := by
      rw [OriginalMovingWindowMoment.width_scale hx0, ← Real.sqrt_eq_rpow, hpower]

/-- The original Mellin adjoint is exactly the inverse-coordinate price integral. -/
theorem adjointKernel_inverse_coordinates {x0 t : ℝ} (hx0 : 4 ≤ x0)
    (ht : 8 ≤ t) (hcut : endpoint x0 ≤ t) (s : ℂ) :
    adjointKernel x0 s t =
      ∫ z in Icc (0 : ℝ) 1,
        (coordinate t z : ℂ) ^ (-s - 1 / 2) *
          ((∫ u in z..1, weightRatio (coordinate t z) u) : ℂ) /
            (((1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)) : ℝ) : ℂ) := by
  have ht0 : 0 < t := by linarith
  have hx1 : 4 ≤ coordinate t 1 := by
    have h := ForwardKernel.Remainder.coordinate_half (by linarith : 2 ≤ t)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    linarith
  have he : endpoint (coordinate t 1) = t := by
    simpa only [one_mul, endpoint] using
      (ForwardKernel.Remainder.coordinate_equation ht0 (show (0 : ℝ) ≤ 1 by norm_num)).symm
  have hlow : x0 ≤ coordinate t 1 := by
    by_contra h
    have hs := OriginalMovingCutRow.endpoint_strictMonoOn
      (show (1 : ℝ) ≤ coordinate t 1 by linarith)
      (show (1 : ℝ) ≤ x0 by linarith) (lt_of_not_ge h)
    rw [he] at hs
    linarith
  have hq : adjointKernel x0 s t =
      ∫ x in Icc (coordinate t 1) t, (x : ℂ) ^ (-s - 1) * (kernel x t : ℂ) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
      (fun x hx => hlow.trans hx.1)
    intro x hx
    by_cases hxt : x < t
    · have hxlo : x < coordinate t 1 := by
        by_contra h
        exact hx.2 ⟨le_of_not_gt h, hxt.le⟩
      have hxx0 : x0 ≤ x := hx.1
      have hs := OriginalMovingCutRow.endpoint_strictMonoOn
        (show (1 : ℝ) ≤ x by linarith)
        (show (1 : ℝ) ≤ coordinate t 1 by linarith) hxlo
      rw [he] at hs
      simp [kernel, not_le.mpr hs]
    · simp [kernel, hxt]
  let d : ℝ → ℝ := fun z => -width (coordinate t z) /
    (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))
  have hd : ∀ z ∈ Ioo (0 : ℝ) 1, HasDerivAt (coordinate t) (d z) z :=
    fun z hz => ForwardKernel.Remainder.coordinate_parameter_hasDerivAt ht0 hz
  have hd0 : ∀ z ∈ Ioo (0 : ℝ) 1, d z ≤ 0 := by
    intro z hz
    have hx := ForwardKernel.Remainder.coordinate_pos ht0 hz.1.le
    dsimp [d]
    have hz0 : 0 ≤ z := hz.1.le
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.rpow_nonneg hx.le _)) (by positivity)
  have hchange := integral_Icc_deriv_smul_of_deriv_nonpos
    (g := fun x : ℝ => (x : ℂ) ^ (-s - 1) * (kernel x t : ℂ))
    (ForwardKernel.Remainder.coordinate_continuousOn_parameter ht0) hd hd0
    (show (0 : ℝ) ≤ 1 by norm_num)
  rw [ForwardKernel.Remainder.coordinate_parameter_zero ht0, ← hq] at hchange
  have hneg : adjointKernel x0 s t = ∫ z in Icc (0 : ℝ) 1,
      ((-d z : ℝ) : ℂ) *
        ((coordinate t z : ℂ) ^ (-s - 1) * (kernel (coordinate t z) t : ℂ)) := by
    simp only [Complex.real_smul] at hchange
    rw [show (fun z => ((-d z : ℝ) : ℂ) *
        ((coordinate t z : ℂ) ^ (-s - 1) * (kernel (coordinate t z) t : ℂ))) =
        (fun z => -((d z : ℂ) *
          ((coordinate t z : ℂ) ^ (-s - 1) * (kernel (coordinate t z) t : ℂ)))) by
      funext z; push_cast; ring, integral_neg, hchange, neg_neg]
  rw [hneg, integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro z hz
  dsimp [d]
  rw [neg_div, neg_neg]
  exact transformed_integrand ht hz s

#print axioms adjointKernel_inverse_coordinates

/-- Beyond the initial window, the literal adjoint is the normalized triangular adjoint. -/
theorem adjointKernel_eq_inverseAdjoint {x0 t : ℝ} (hx0 : 4 ≤ x0)
    (ht : 8 ≤ t) (hcut : endpoint x0 ≤ t) (s : ℂ) :
    adjointKernel x0 s t = ForwardKernel.Asymptotic.inverseAdjoint t s := by
  rw [adjointKernel_inverse_coordinates hx0 ht hcut s,
    ForwardKernel.Asymptotic.inverseAdjoint_eq_iterated ht s]
  simp only [intervalIntegral.integral_ofReal]

#print axioms adjointKernel_eq_inverseAdjoint

end

end D5.S3.Arith.Robin.ForwardKernel.InverseTransport
