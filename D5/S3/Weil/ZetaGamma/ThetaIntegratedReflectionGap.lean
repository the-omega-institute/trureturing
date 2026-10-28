/- GID: D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap
   mirror-E: none(waiver:universal-infinite-analytic-estimate)
   anchors: []
   utility: none
   digest: The complete reflected physical kernel has an integrable positive separation reserve. -/

import D5.S3.Weil.ZetaGamma.ThetaReflectedQuantitativeGap
import Batteries.Tactic.OpenPrivate

noncomputable section

namespace D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison

open Real Set MeasureTheory Filter
open D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open private p d radialStart radialProduct radialIntegrand phi_pos
  radialIntegrand_continuous radialIntegrand_integrable pd_geometry
  physicalKernel_radial_identity physicalKernel_reflected_radial_identity
  from D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison

/-- The first radial excess moment of the complete reflected entry.
The lower endpoint is r0=((a+b)/2)^2+(|a-b|/2)^2; no radial cutoff is used. -/
def reflectedRadialMoment (v a b : ℝ) : ℝ :=
  ∫ r in Ioi (radialStart a b),
    (r - radialStart a b) * radialIntegrand v (p a b) r

private theorem radialIntegrand_abs_weight (v c r : ℝ) :
    radialIntegrand |v| c r = radialIntegrand v c r := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv]
  · dsimp only [radialIntegrand]
    rw [abs_of_neg (lt_of_not_ge hv),
      show 2 * -v * sqrt (r - c ^ 2) = -(2 * v * sqrt (r - c ^ 2)) by ring,
      cosh_neg]

/-- The pointwise curvature reserve survives integration over the entire
physical domain. Both the moment and the strictly positive remainder are L1. -/
theorem physical_kernel_integrated_gap {a b v : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    0 < reflectedRadialMoment v a b ∧
      (a * b / 24) * reflectedRadialMoment v a b <
        physicalKernel v a b - physicalKernel v a (-b) := by
  let r0 := radialStart a b
  let J : ℝ → ℝ := fun r => (r - r0) * radialIntegrand v (p a b) r
  let C : ℝ → ℝ := fun r => (a * b / 6) * J r
  let Δ : ℝ → ℝ := fun r =>
    radialIntegrand v (d a b) r - radialIntegrand v (p a b) r
  have hpd := pd_geometry ha hb
  have hid : IntegrableOn (radialIntegrand v (d a b)) (Ioi r0) :=
    radialIntegrand_integrable v (d a b) (p a b)
  have hip : IntegrableOn (radialIntegrand v (p a b)) (Ioi r0) := by
    simpa only [r0, radialStart, add_comm] using
      radialIntegrand_integrable v (p a b) (d a b)
  have hΔint : IntegrableOn Δ (Ioi r0) := hid.sub hip
  have hJpos (r : ℝ) (hr : r ∈ Ioi r0) : 0 < J r := by
    exact mul_pos (sub_pos.mpr hr)
      (mul_pos (cosh_pos _) (mul_pos (phi_pos _) (phi_pos _)))
  have hCnonneg (r : ℝ) (hr : r ∈ Ioi r0) : 0 ≤ C r :=
    (mul_pos (by positivity : 0 < a * b / 6) (hJpos r hr)).le
  have hClt (r : ℝ) (hr : r ∈ Ioi r0) (hne : r ≠ 2 * (p a b) ^ 2) :
      C r < Δ r := by
    have h := physical_kernel_gap_quantitative ha hb (abs_nonneg v) hr hne
    simp only [radialIntegrand_abs_weight] at h
    dsimp only [C, J, Δ, r0]
    nlinarith [h]
  have hCcont : Continuous C :=
    continuous_const.mul
      ((continuous_id.sub continuous_const).mul (radialIntegrand_continuous v (p a b)))
  have hCint : IntegrableOn C (Ioi r0) := by
    apply hΔint.mono' hCcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne (2 * (p a b) ^ 2))] with r hr hne
    rw [Real.norm_eq_abs, abs_of_nonneg (hCnonneg r hr)]
    exact (hClt r hr hne).le
  have hscale : (fun r => (6 / (a * b)) * C r) = J := by
    funext r
    dsimp only [C]
    field_simp [ne_of_gt ha, ne_of_gt hb] <;> ring
  have hJint : IntegrableOn J (Ioi r0) := by
    rw [← hscale]
    exact hCint.const_mul _
  have hJnn : 0 ≤ᵐ[volume.restrict (Ioi r0)] J := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hJpos r hr).le
  have hJsub : Ioo r0 (r0 + 1) ⊆ Function.support J ∩ Ioi r0 := by
    intro r hr
    exact ⟨ne_of_gt (hJpos r hr.1), hr.1⟩
  have hJμ : 0 < volume (Ioo r0 (r0 + 1)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hJintegralpos : 0 < ∫ r in Ioi r0, J r :=
    (setIntegral_pos_iff_support_of_nonneg_ae hJnn hJint).mpr
      (hJμ.trans_le (measure_mono hJsub))
  have hRint : IntegrableOn (fun r => Δ r - C r) (Ioi r0) := hΔint.sub hCint
  have hRnn : 0 ≤ᵐ[volume.restrict (Ioi r0)] (fun r => Δ r - C r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne (2 * (p a b) ^ 2))] with r hr hne
    exact (sub_pos.mpr (hClt r hr hne)).le
  have hwidth : r0 < 2 * (p a b) ^ 2 := by
    dsimp only [r0, radialStart]
    nlinarith [mul_pos (sub_pos.mpr hpd.2)
      (by linarith [hpd.1] : 0 < p a b + d a b)]
  have hRsub : Ioo r0 (2 * (p a b) ^ 2) ⊆
      Function.support (fun r => Δ r - C r) ∩ Ioi r0 := by
    intro r hr
    exact ⟨ne_of_gt (sub_pos.mpr (hClt r hr.1 (ne_of_lt hr.2))), hr.1⟩
  have hRμ : 0 < volume (Ioo r0 (2 * (p a b) ^ 2)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hwidth)
  have hRpos : 0 < ∫ r in Ioi r0, Δ r - C r :=
    (setIntegral_pos_iff_support_of_nonneg_ae hRnn hRint).mpr
      (hRμ.trans_le (measure_mono hRsub))
  rw [integral_sub hΔint hCint] at hRpos
  change 0 < (∫ r in Ioi r0,
    radialIntegrand v (d a b) r - radialIntegrand v (p a b) r) -
    ∫ r in Ioi r0, (a * b / 6) * J r at hRpos
  rw [integral_sub hid hip, integral_const_mul] at hRpos
  refine ⟨hJintegralpos, ?_⟩
  change (a * b / 24) * (∫ r in Ioi r0, J r) < _
  rw [physicalKernel_radial_identity ha hb, physicalKernel_reflected_radial_identity ha hb]
  change (a * b / 24) * (∫ r in Ioi r0, J r) <
    (1 / 4 : ℝ) * (∫ r in Ioi r0, radialIntegrand v (d a b) r) -
    (1 / 4 : ℝ) * (∫ r in Ioi r0, radialIntegrand v (p a b) r)
  nlinarith [hRpos]

#print axioms physical_kernel_integrated_gap

end D5.S3.Weil.ZetaGamma.ThetaReflectedKernelComparison
