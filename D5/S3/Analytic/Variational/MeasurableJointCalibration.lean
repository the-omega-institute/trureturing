/- GID: D5/S3/Analytic/Variational/MeasurableJointCalibration
   generality: G
   mirror-B: D5/B/S3/Analytic/Variational/MeasurableJointCalibration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrable square remainder and zero-energy transport for measurable calibration. -/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Tactic

/-! # Quantitative measurable calibration and transport rigidity -/

open Set Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace D5.S3.Analytic.Variational.MeasurableJointCalibration

/-- Smooth reference data; no regularity is required of a competing density. -/
structure Calibration (b : ℝ) (Z Q M N : ℝ → ℝ) : Prop where
  smoothZ : ∀ r ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ Z r
  smoothM : ∀ r ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ M r
  continuousQ : ContinuousOn Q (Icc (0 : ℝ) 1)
  derivZ : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt Z (Q r) r
  derivM : ∀ r ∈ Icc (0 : ℝ) 1, HasDerivAt M (N r) r
  coefficients : ∀ r ∈ Icc (0 : ℝ) 1,
    0 < Z r ∧ 0 < Q r ∧
      M r = 8 * b * Q r / 9 + 8 * r * Q r ^ 2 / (9 * Z r) ∧
      N r = -8 * r * Q r ^ 3 / (27 * Z r ^ 2)

/-- The defect is in the original square-root reciprocal coordinates. -/
def defect (u U Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  u x * (Real.sqrt x / u x - (2 / 3 : ℝ) * Q (U x)) ^ 2

/-- The calibrated absolutely continuous comparison function. -/
def potential (U Z M : ℝ → ℝ) (x : ℝ) : ℝ :=
  M (U x) * (x * Real.sqrt x - Z (U x) / 2)

private lemma support {b r z q Z Q : ℝ} (hr : 0 ≤ r)
    (hz : 0 < z) (hq : 0 ≤ q) (hZ : 0 < Z) (hQ : 0 < Q) :
    (-8 * r * Q ^ 3 / (27 * Z ^ 2)) * z +
      (8 * b * Q / 9 + 8 * r * Q ^ 2 / (9 * Z)) * q -
      ((-8 * r * Q ^ 3 / (27 * Z ^ 2)) * Z +
        (8 * b * Q / 9 + 8 * r * Q ^ 2 / (9 * Z)) * Q) / 2 +
      4 * b / 9 * (q - Q) ^ 2 ≤
      4 * b * q ^ 2 / 9 + 8 * r * q ^ 3 / (27 * z) := by
  have hp : 0 ≤ q ^ 3 * Z ^ 2 + Q ^ 3 * z ^ 2 + Q ^ 3 * z * Z -
      3 * Q ^ 2 * q * z * Z := by
    by_cases h : q ≤ Q / 3
    · have hn : 0 ≤ Q ^ 2 * z * Z * (Q - 3 * q) := by
        apply mul_nonneg (by positivity) (by linarith)
      nlinarith [mul_nonneg (pow_nonneg hq 3) (sq_nonneg Z),
        mul_nonneg (pow_nonneg hQ.le 3) (sq_nonneg z)]
    · have hn : 0 ≤ Q * (2 * Q * z - 3 * q * Z + Q * Z) ^ 2 +
          Z ^ 2 * (q - Q) ^ 2 * (4 * q - Q) := by
        apply add_nonneg (by positivity)
        exact mul_nonneg (mul_nonneg (sq_nonneg Z) (sq_nonneg (q - Q)))
          (by linarith)
      have he : 4 * (q ^ 3 * Z ^ 2 + Q ^ 3 * z ^ 2 + Q ^ 3 * z * Z -
          3 * Q ^ 2 * q * z * Z) =
          Q * (2 * Q * z - 3 * q * Z + Q * Z) ^ 2 +
            Z ^ 2 * (q - Q) ^ 2 * (4 * q - Q) := by ring
      linarith
  have hg : 0 ≤ q ^ 3 / z -
      (Q ^ 3 / Z - Q ^ 3 / Z ^ 2 * (z - Z) + 3 * Q ^ 2 / Z * (q - Q)) := by
    apply nonneg_of_mul_nonneg_right (a := z * Z ^ 2) ?_ (by positivity)
    convert hp using 1 <;> field_simp <;> ring
  have hn := mul_nonneg (show 0 ≤ 8 * r / 27 by positivity) hg
  have he : 4 * b * q ^ 2 / 9 + 8 * r * q ^ 3 / (27 * z) -
      ((-8 * r * Q ^ 3 / (27 * Z ^ 2)) * z +
        (8 * b * Q / 9 + 8 * r * Q ^ 2 / (9 * Z)) * q -
        ((-8 * r * Q ^ 3 / (27 * Z ^ 2)) * Z +
          (8 * b * Q / 9 + 8 * r * Q ^ 2 / (9 * Z)) * Q) / 2 +
        4 * b / 9 * (q - Q) ^ 2) =
      8 * r / 27 * (q ^ 3 / z -
        (Q ^ 3 / Z - Q ^ 3 / Z ^ 2 * (z - Z) + 3 * Q ^ 2 / Z * (q - Q))) := by
    field_simp; ring
  linarith

private lemma space_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => t * Real.sqrt t) (3 * Real.sqrt x / 2) x := by
  have hs := Real.sq_sqrt hx.le
  convert (hasDerivAt_id x).mul (Real.hasDerivAt_sqrt (ne_of_gt hx)) using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [ne_of_gt (Real.sqrt_pos.2 hx)]
    nlinarith

private lemma space_ac :
    AbsolutelyContinuousOnInterval (fun x : ℝ => x * Real.sqrt x) 1 2 := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  intro x hx
  have hxpos : 0 < x := by
    rw [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] at hx
    linarith [hx.1]
  exact (contDiffAt_id.mul (Real.contDiffAt_sqrt (ne_of_gt hxpos))).contDiffWithinAt

private lemma compose_ac {F U : ℝ → ℝ}
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F r)
    (hU : AbsolutelyContinuousOnInterval U 1 2)
    (hmap : MapsTo U (Icc (1 : ℝ) 2) (Icc (0 : ℝ) 1)) :
    AbsolutelyContinuousOnInterval (F ∘ U) 1 2 := by
  have hc : ContDiffOn ℝ ∞ F (Icc (0 : ℝ) 1) :=
    fun r hr => (hF r hr).contDiffWithinAt
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by simp) (convex_Icc _ _) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval
    (by simpa only [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using hmap) hU

private lemma defect_integrable {u U Q : ℝ → ℝ}
    (hu : AEMeasurable u (volume.restrict (Icc (1 : ℝ) 2)))
    {c B : ℝ} (hc : 0 < c)
    (hbounds : ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2), c ≤ u x ∧ u x ≤ B)
    (hU : AbsolutelyContinuousOnInterval U 1 2)
    (hmap : MapsTo U (Icc (1 : ℝ) 2) (Icc (0 : ℝ) 1))
    (hQ : ContinuousOn Q (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (defect u U Q) volume 1 2 := by
  have hUc : ContinuousOn U (Icc (1 : ℝ) 2) := by
    simpa only [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using hU.continuousOn
  have hQc := hQ.comp hUc hmap
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hQc
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2
  have hm : AEMeasurable (Q ∘ U) (volume.restrict (Icc (1 : ℝ) 2)) :=
    (hQc.aestronglyMeasurable measurableSet_Icc).aemeasurable
  apply Integrable.of_bound
    (hu.mul (((Real.continuous_sqrt.measurable.aemeasurable.div hu).sub
      (hm.const_mul (2 / 3 : ℝ))).pow_const 2)).aestronglyMeasurable
    (B * (2 / c + (2 / 3 : ℝ) * K) ^ 2)
  filter_upwards [hbounds, ae_restrict_mem measurableSet_Icc] with x hx hxmem
  have hup : 0 < u x := hc.trans_le hx.1
  have hs : ‖Real.sqrt x / u x‖ ≤ 2 / c := by
    rw [norm_div, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg hup.le]
    apply (div_le_div_iff₀ hup hc).2
    have hroot : Real.sqrt x ≤ 2 := by
      have := Real.sq_sqrt (show 0 ≤ x by linarith [hxmem.1])
      nlinarith [Real.sqrt_nonneg x, hxmem.2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hc.le]
  have ht : ‖Real.sqrt x / u x - (2 / 3 : ℝ) * Q (U x)‖ ≤
      2 / c + (2 / 3 : ℝ) * K := by
    calc
      _ ≤ ‖Real.sqrt x / u x‖ + ‖(2 / 3 : ℝ) * Q (U x)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)]
        gcongr
        exact hK x hxmem
  change ‖u x * _ ^ 2‖ ≤ _
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hup.le]
  exact mul_le_mul hx.2 (pow_le_pow_left₀ (norm_nonneg _) ht 2) (by positivity)
    (hc.le.trans hx.1 |>.trans hx.2)

/-- Individual positive bounds suffice for all three reciprocal integrals. -/
theorem bounded_positive_integrability {u : ℝ → ℝ}
    (hu : AEMeasurable u (volume.restrict (Icc (1 : ℝ) 2)))
    (hbounds : ∃ c B : ℝ, 0 < c ∧
      ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2), c ≤ u x ∧ u x ≤ B) :
    IntervalIntegrable u volume 1 2 ∧
    IntervalIntegrable (fun x => x / u x) volume 1 2 ∧
    IntervalIntegrable (fun x => (∫ s in (1 : ℝ)..x, u s) / u x ^ 2) volume 1 2 := by
  obtain ⟨c, B, hc, hbounds⟩ := hbounds
  have hi : IntegrableOn u (Icc (1 : ℝ) 2) volume :=
    Integrable.of_bound hu.aestronglyMeasurable B (hbounds.mono fun x hx => by
      rw [Real.norm_of_nonneg (by linarith [hx.1])]
      exact hx.2)
  have hii : IntervalIntegrable u volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hi
  have huc : ContinuousOn ((fun x : ℝ => ∫ s in (1 : ℝ)..x, u s)) (Icc (1 : ℝ) 2) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (1 : ℝ))
      hii left_mem_uIcc
    rw [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] at h
    exact h
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn huc
  have hlag : IntegrableOn (fun x => x / u x) (Icc (1 : ℝ) 2) volume := by
    apply Integrable.of_bound
      (measurable_id.aemeasurable.div hu).aestronglyMeasurable (2 / c)
    filter_upwards [hbounds, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    have hup : 0 < u x := hc.trans_le hx.1
    change ‖x / u x‖ ≤ 2 / c
    rw [norm_div, Real.norm_of_nonneg (by linarith [hxmem.1]),
      Real.norm_of_nonneg hup.le]
    apply (div_le_div_iff₀ hup hc).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hxmem.2) hc.le]
  have hfuture : IntegrableOn (fun x => (fun x : ℝ => ∫ s in (1 : ℝ)..x, u s) x / u x ^ 2)
      (Icc (1 : ℝ) 2) volume := by
    have hmeas : AEMeasurable ((fun x : ℝ => ∫ s in (1 : ℝ)..x, u s)) (volume.restrict (Icc (1 : ℝ) 2)) :=
      (huc.aestronglyMeasurable measurableSet_Icc).aemeasurable
    apply Integrable.of_bound (hmeas.div (hu.pow_const 2)).aestronglyMeasurable
      (M / c ^ 2)
    filter_upwards [hbounds, ae_restrict_mem measurableSet_Icc] with x hx hxmem
    have hup : 0 < u x := hc.trans_le hx.1
    have hsq : c ^ 2 ≤ u x ^ 2 := by nlinarith [hx.1]
    change ‖(fun x : ℝ => ∫ s in (1 : ℝ)..x, u s) x / u x ^ 2‖ ≤ M / c ^ 2
    rw [norm_div, norm_pow, Real.norm_of_nonneg hup.le]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hc) hsq).trans
      (div_le_div_of_nonneg_right (hM x hxmem) (sq_nonneg c))
  exact ⟨hii,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hlag,
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hfuture⟩

/-- Global square remainder and zero-energy transport for the full measurable class.
The calibration equations are hypotheses only on the smooth reference. -/
theorem remainder {b : ℝ} {Z Q M N u U : ℝ → ℝ}
    (hcal : Calibration b Z Q M N)
    (hu : AEMeasurable u (volume.restrict (Icc (1 : ℝ) 2)))
    (hbounds : ∃ c B : ℝ, 0 < c ∧
      ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2), c ≤ u x ∧ u x ≤ B)
    (hU : AbsolutelyContinuousOnInterval U 1 2)
    (hmap : MapsTo U (Icc (1 : ℝ) 2) (Icc (0 : ℝ) 1))
    (hdU : ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2), HasDerivAt U (u x) x)
    (hL : IntervalIntegrable (fun x => b * (x / u x) + U x / u x ^ 2) volume 1 2)
    (hU1 : U 1 = 0) (hZ0 : Z 0 = 1) :
    IntervalIntegrable (defect u U Q) volume 1 2 ∧
    0 ≤ ∫ x in (1 : ℝ)..2, defect u U Q x ∧
    potential U Z M 2 - potential U Z M 1 +
        b * (∫ x in (1 : ℝ)..2, defect u U Q x) ≤
      ∫ x in (1 : ℝ)..2, b * (x / u x) + U x / u x ^ 2 ∧
    ((∫ x in (1 : ℝ)..2, defect u U Q x) = 0 →
      (∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2),
        Real.sqrt x / u x = (2 / 3 : ℝ) * Q (U x)) ∧
      ∀ x ∈ Icc (1 : ℝ) 2, Z (U x) = x * Real.sqrt x) := by
  obtain ⟨c, B, hc, hbounds⟩ := hbounds
  have hi := defect_integrable hu hc hbounds hU hmap hcal.continuousQ
  have hn : 0 ≤ᵐ[volume.restrict (Icc (1 : ℝ) 2)] defect u U Q :=
    hbounds.mono (fun x hx => mul_nonneg (hc.le.trans hx.1) (sq_nonneg _))
  have hZac := compose_ac hcal.smoothZ hU hmap
  have hMac := compose_ac hcal.smoothM hU hmap
  have hVac : AbsolutelyContinuousOnInterval (potential U Z M) 1 2 := by
    convert hMac.mul (space_ac.sub (hZac.const_mul (1 / 2))) using 1
    funext x; dsimp [potential]; ring
  have hle : ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2),
      deriv (potential U Z M) x + b * defect u U Q x ≤
        b * (x / u x) + U x / u x ^ 2 := by
    filter_upwards [hbounds, ae_restrict_mem measurableSet_Icc, hdU] with x hux hx hd
    have hup : 0 < u x := hc.trans_le hux.1
    have hxpos : 0 < x := by linarith [hx.1]
    have hr := hmap hx
    have hV := ((hcal.derivM _ hr).comp x hd).mul
      ((space_deriv hxpos).sub (((hcal.derivZ _ hr).comp x hd).div_const 2))
    change HasDerivAt (potential U Z M) _ x at hV
    rw [hV.deriv]
    obtain ⟨hZpos, hQpos, hMeq, hNeq⟩ := hcal.coefficients _ hr
    have hs := support (b := b) hr.1 (mul_pos hxpos (Real.sqrt_pos.2 hxpos))
      (show 0 ≤ 3 * Real.sqrt x / (2 * u x) by positivity) hZpos hQpos
    rw [← hMeq, ← hNeq] at hs
    have hle := mul_le_mul_of_nonneg_left hs hup.le
    convert hle using 1
    · dsimp only [defect, Pi.sub_apply, Function.comp_apply]
      field_simp [ne_of_gt hup]; ring
    · field_simp [ne_of_gt hup, ne_of_gt hxpos, ne_of_gt (Real.sqrt_pos.2 hxpos)]
      have hsq := Real.sq_sqrt hxpos.le
      generalize Real.sqrt x = t at *
      rw [← hsq]; ring
  have hbound := intervalIntegral.integral_mono_ae_restrict
    (show (1 : ℝ) ≤ 2 by norm_num)
    (hVac.intervalIntegrable_deriv.add (hi.const_mul b)) hL hle
  rw [intervalIntegral.integral_add hVac.intervalIntegrable_deriv (hi.const_mul b),
    hVac.integral_deriv_eq_sub, intervalIntegral.integral_const_mul] at hbound
  refine ⟨hi, intervalIntegral.integral_nonneg_of_ae_restrict (by norm_num) hn, hbound, ?_⟩
  intro he
  have hie : IntegrableOn (defect u U Q) (Icc (1 : ℝ) 2) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1 hi
  have he' : (∫ x in Icc (1 : ℝ) 2, defect u U Q x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    exact he
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hie).1 he'
  have hslope : ∀ᵐ x ∂volume.restrict (Icc (1 : ℝ) 2),
      Real.sqrt x / u x = (2 / 3 : ℝ) * Q (U x) := by
    filter_upwards [hz, hbounds] with x hx hux
    have hup : 0 < u x := hc.trans_le hux.1
    have hs : (Real.sqrt x / u x - (2 / 3 : ℝ) * Q (U x)) ^ 2 = 0 :=
      (mul_eq_zero.mp hx).resolve_left (ne_of_gt hup)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  refine ⟨hslope, ?_⟩
  have hHac := hZac.sub space_ac
  have hdH : ∀ᵐ x, x ∈ uIcc (1 : ℝ) 2 →
      HasDerivAt (fun t => Z (U t) - t * Real.sqrt t) 0 x := by
    rw [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)]
    apply (ae_restrict_iff' measurableSet_Icc).1
    filter_upwards [hslope, hbounds, hdU, ae_restrict_mem measurableSet_Icc]
      with x hs hux hd hxmem
    have hup : 0 < u x := hc.trans_le hux.1
    have hdv := ((hcal.derivZ _ (hmap hxmem)).comp x hd).sub
      (space_deriv (show 0 < x by linarith [hxmem.1]))
    have heq := (div_eq_iff (ne_of_gt hup)).1 hs
    have hd0 : Q (U x) * u x - 3 * Real.sqrt x / 2 = 0 := by nlinarith
    rw [hd0] at hdv
    exact hdv
  obtain ⟨C, hC⟩ := hHac.const_of_ae_hasDerivAt_zero hdH
  have hC0 := hC 1 (by norm_num)
  change Z (U 1) - 1 * Real.sqrt 1 = C at hC0
  simp only [hU1, hZ0, Real.sqrt_one, one_mul, sub_self] at hC0
  intro x hx
  have hx' := hC x (by simpa only [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using hx)
  dsimp only [Function.comp_apply, Pi.sub_apply] at hx'
  linarith

/-- A.e. representatives give exactly the same cumulative mass at every initial interval. -/
theorem primitive_congr {u v : ℝ → ℝ}
    (h : u =ᵐ[volume.restrict (Icc (1 : ℝ) 2)] v) {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
    (∫ t in (1 : ℝ)..x, u t) = ∫ t in (1 : ℝ)..x, v t := by
  apply intervalIntegral.integral_congr_ae_restrict
  have hs : uIoc (1 : ℝ) x ⊆ Icc (1 : ℝ) 2 := by
    rw [uIoc_of_le hx.1]
    exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hx.2)
  exact h.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))

end D5.S3.Analytic.Variational.MeasurableJointCalibration
