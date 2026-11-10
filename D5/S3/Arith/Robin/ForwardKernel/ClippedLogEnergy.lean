/- GID: D5/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/ClippedLogEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Clipping a logarithmic cusp gives a uniform linear translation-energy bound. -/

import D5.S3.Analytic.LogSquareBound
import D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpnessDefs
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Asymptotics

/-! Uniform translation energy for clipped logarithmic cusps. -/

namespace D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

/-- Local square integrability of the logarithm, used for the cusp averages. -/
theorem intervalIntegrable_log_sq (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (Real.log x) ^ 2) volume a b := by
  apply intervalIntegrable_of_even (fun x => by rw [Real.log_neg_eq_log])
  intro x hx
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le]
  have hmaj : IntervalIntegrable (fun t : ℝ => 16 * t ^ (-1/2 : ℝ) + t ^ 2)
      volume 0 x :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -1/2)).const_mul 16).add
      ((continuous_pow 2).intervalIntegrable 0 x)
  refine ((intervalIntegrable_iff_integrableOn_Ioo_of_le hx.le).mp hmaj).mono'
    (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [norm_pow, Real.norm_eq_abs, sq_abs] using
    D5.S3.Analytic.LogSquareBound.log_square_bound t ht.1

/-- The clipped cusp is continuous, including its inner plateau. -/
theorem clippedLog_continuous {h k : ℝ} (hh : 0 < h) (hhk : h < k) :
    Continuous (clippedLog h k) := by
  have hk : 0 < k := hh.trans hhk
  apply Continuous.log
  · exact (continuous_const.min (continuous_const.max continuous_abs)).div_const k
  · intro y
    exact ne_of_gt (div_pos (lt_min hk (hh.trans_le (le_max_left _ _))) hk)

private theorem logJump_sq_integrableOn (a b : ℝ) :
    IntegrableOn (fun z : ℝ => logJump z ^ 2) (Icc a b) := by
  by_cases hab : a ≤ b
  · have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      (intervalIntegrable_log_sq a b)
    have hj : IntegrableOn (fun z : ℝ => (Real.log (z + 1)) ^ 2) (Icc a b) := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      convert (intervalIntegrable_log_sq (a + 1) (b + 1)).comp_add_right 1 using 1 <;> simp
    have hm : Measurable logJump := by
      change Measurable (fun z : ℝ => Real.log |z + 1| - Real.log |z|)
      simp only [Real.log_abs]
      exact (Real.measurable_log.comp (measurable_id.add_const 1)).sub Real.measurable_log
    refine ((hj.add hi).const_mul 2).mono' (hm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with z
    simp only [logJump, Real.log_abs, norm_pow, Real.norm_eq_abs, sq_abs,
      Pi.add_apply]
    nlinarith [sq_nonneg (Real.log (z + 1) + Real.log z)]
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge hab)]

private theorem logJump_tail_bound {z : ℝ} (hz : 2 ≤ |z|) :
    |logJump z| ≤ 2 / |z| := by
  have hB : 0 < |z| := by linarith
  have hAB : |z + 1| ≤ |z| + 1 := by simpa using abs_add_le z 1
  have hBA : |z| ≤ |z + 1| + 1 := by
    simpa using abs_sub (z + 1) 1
  have hA : 0 < |z + 1| := by linarith
  have hupper := Real.log_le_sub_one_of_pos (div_pos hA hB)
  rw [Real.log_div hA.ne' hB.ne'] at hupper
  have hupper' := mul_le_mul_of_nonneg_right hupper hB.le
  simp only [sub_mul, div_mul_cancel₀ _ hB.ne', one_mul] at hupper'
  have hlower := Real.log_le_sub_one_of_pos (div_pos hB hA)
  rw [Real.log_div hB.ne' hA.ne'] at hlower
  have hlower' := mul_le_mul_of_nonneg_right hlower hA.le
  simp only [sub_mul, div_mul_cancel₀ _ hA.ne', one_mul] at hlower'
  have hlow : Real.log |z| - Real.log |z + 1| ≤ 1 / |z + 1| := by
    apply (le_div_iff₀ hA).mpr
    linarith
  have hi : 1 / |z + 1| ≤ 2 / |z| := by
    apply (div_le_div_iff₀ hA hB).mpr
    linarith
  rw [abs_le]
  constructor
  · dsimp [logJump]; linarith
  · dsimp [logJump]
    apply (le_div_iff₀ hB).mpr
    linarith

private theorem logJump_sq_tail_bound {z : ℝ} (hz : 2 ≤ |z|) :
    ‖logJump z ^ 2‖ ≤ 4 * |z| ^ (-2 : ℝ) := by
  have hh := pow_le_pow_left₀ (abs_nonneg (logJump z)) (logJump_tail_bound hz) 2
  calc
    ‖logJump z ^ 2‖ = |logJump z| ^ 2 := by rw [norm_pow, Real.norm_eq_abs]
    _ ≤ (2 / |z|) ^ 2 := hh
    _ = 4 * |z| ^ (-2 : ℝ) := by
      rw [div_pow, Real.rpow_neg (abs_nonneg z), Real.rpow_two]
      norm_num [div_eq_mul_inv]

/-- The untruncated unit logarithmic jump has finite square energy. -/
theorem logJump_sq_integrable : Integrable (fun z : ℝ => logJump z ^ 2) := by
  have hl : LocallyIntegrable (fun z : ℝ => logJump z ^ 2) := by
    intro z
    exact ⟨Icc (z - 1) (z + 1), Icc_mem_nhds (by linarith) (by linarith),
      logJump_sq_integrableOn _ _⟩
  have hg : IntegrableAtFilter (fun z : ℝ => |z| ^ (-2 : ℝ)) atTop volume := by
    refine ⟨Ioi 2, Ioi_mem_atTop _, ?_⟩
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 2)).congr_fun ?_ measurableSet_Ioi
    intro z hz
    dsimp only
    rw [abs_of_pos (by linarith [hz.out] : 0 < z)]
  have hg' : IntegrableAtFilter (fun z : ℝ => |z| ^ (-2 : ℝ)) atBot volume := by
    obtain ⟨s, hs, hi⟩ := hg
    refine ⟨Neg.neg ⁻¹' s, tendsto_neg_atBot_atTop hs, ?_⟩
    have hh : IntegrableOn (fun z : ℝ => |-z| ^ (-2 : ℝ)) (Neg.neg ⁻¹' s) :=
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding).mpr hi
    simpa only [abs_neg] using hh
  apply hl.integrable_of_isBigO_atBot_atTop _ hg' _ hg
  · refine Asymptotics.IsBigO.of_bound 4 ?_
    filter_upwards [eventually_le_atBot (-2 : ℝ)] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) _)] using
      logJump_sq_tail_bound (z := z) (by rw [abs_of_nonpos (by linarith)]; linarith)
  · refine Asymptotics.IsBigO.of_bound 4 ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg z) _)] using
      logJump_sq_tail_bound (z := z) (by rw [abs_of_nonneg (by linarith)]; exact hz)

theorem clippedLog_log_space {h k y : ℝ} (hh : 0 < h) (hhk : h < k)
    (hy : y ≠ 0) :
    clippedLog h k y =
      min (Real.log k) (max (Real.log h) (Real.log |y|)) - Real.log k := by
  have hk := hh.trans hhk
  have hm : 0 < max h |y| := hh.trans_le (le_max_left _ _)
  rw [clippedLog, Real.log_div (ne_of_gt (lt_min hk hm)) hk.ne',
    Real.strictMonoOn_log.monotoneOn.map_min hk hm,
    Real.strictMonoOn_log.monotoneOn.map_max hh (abs_pos.mpr hy)]

private theorem clippedLog_log_contraction {h k x y : ℝ}
    (hh : 0 < h) (hhk : h < k) (hx : x ≠ 0) (hy : y ≠ 0) :
    |clippedLog h k x - clippedLog h k y| ≤ |Real.log (|x|) - Real.log (|y|)| := by
  have hc : LipschitzWith 1
      (fun v : ℝ => min (Real.log k) (max (Real.log h) v)) :=
    (LipschitzWith.id.const_max (Real.log h)).const_min (Real.log k)
  rw [clippedLog_log_space hh hhk hx, clippedLog_log_space hh hhk hy,
    sub_sub_sub_cancel_right]
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    hc.dist_le_mul (Real.log |x|) (Real.log |y|)

private theorem logJump_rescale {y u : ℝ} (hu : 0 < u) (hy : y ≠ 0)
    (hyu : y + u ≠ 0) :
    Real.log |y + u| - Real.log |y| = logJump (y / u) := by
  rw [logJump, show y / u + 1 = (y + u) / u by field_simp]
  rw [abs_div, abs_div, abs_of_pos hu,
    Real.log_div (abs_ne_zero.mpr hyu) hu.ne',
    Real.log_div (abs_ne_zero.mpr hy) hu.ne']
  ring

/-- The translation square is integrable and bounded by an absolute constant times the step.
The constant is independent of both clipping radii; sparse-spike variance uses this bound. -/
theorem clippedLog_translation_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ h k u : ℝ,
      0 < h → h < k → 0 < u →
        Integrable (fun y : ℝ => (clippedLog h k (y + u) - clippedLog h k y) ^ 2) ∧
        (∫ y : ℝ, (clippedLog h k (y + u) - clippedLog h k y) ^ 2) ≤ C * u := by
  let J : ℝ := ∫ z : ℝ, logJump z ^ 2
  have hJ : 0 ≤ J := integral_nonneg (fun z => sq_nonneg (logJump z))
  refine ⟨J + 1, by positivity, ?_⟩
  intro h k u hh hhk hu
  have hi := logJump_sq_integrable.comp_div hu.ne'
  have hb : ∀ᵐ y : ℝ,
      (clippedLog h k (y + u) - clippedLog h k y) ^ 2 ≤ logJump (y / u) ^ 2 := by
    filter_upwards [Measure.ae_ne volume 0, Measure.ae_ne volume (-u)] with y hy hym
    have hyu : y + u ≠ 0 := by
      intro he
      apply hym
      linarith
    have hc := clippedLog_log_contraction hh hhk hyu hy
    rw [logJump_rescale hu hy hyu] at hc
    have hs := pow_le_pow_left₀ (abs_nonneg _) hc 2
    simpa only [sq_abs] using hs
  have hf : Integrable (fun y : ℝ =>
      (clippedLog h k (y + u) - clippedLog h k y) ^ 2) := by
    have hfm : Continuous (fun y : ℝ =>
        (clippedLog h k (y + u) - clippedLog h k y) ^ 2) :=
      (((clippedLog_continuous hh hhk).comp (continuous_id.add_const u)).sub
        (clippedLog_continuous hh hhk)).pow 2
    apply hi.mono' hfm.aestronglyMeasurable
    filter_upwards [hb] with y hy
    simpa only [norm_pow, Real.norm_eq_abs, sq_abs] using hy
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ y : ℝ, logJump (y / u) ^ 2 := integral_mono_ae hf hi hb
    _ = u * J := by
      simpa only [abs_of_pos hu, smul_eq_mul] using
        Measure.integral_comp_div (fun z : ℝ => logJump z ^ 2) u
    _ ≤ (J + 1) * u := by nlinarith

end
end D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness
