import D5.S3.Analytic.NativeHalfPowerLip
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitMean

/-! The actual signed half-current mean across one D lip. -/

open Complex Filter Set
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open D5.S3.Analytic.NativeHalfPowerLip
open OriginalFourMPeriodSource (dLip)
open OriginalGaussianExternalAnalyticCandidate (b)
open OriginalGaussianExternalSignedCandidate (h)
open OriginalFourMSlitMean (slitMean)

private def phase (upperA : Bool) : ℂ := if upperA then -I else I

def dLipMean (upperA e : Bool) (u r : ℂ) : ℂ :=
  if e then slitMean e u r
  else (b u)⁻¹ * (phase upperA * (-(h e u r / b u)) ^ (-1 / 2 : ℂ))

theorem dLipMean_joint_analytic (upperA e : Bool) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => dLipMean upperA e p.1 p.2) (0, (t : ℂ)) := by
  have hb : AnalyticAt ℂ (fun p : ℂ × ℂ => b p.1) (0, (t : ℂ)) :=
    analyticAt_const.sub analyticAt_fst
  have hb₀ : b 0 ≠ 0 := by simp [b]
  cases e
  · have hh : AnalyticAt ℂ (fun p : ℂ × ℂ => h false p.1 p.2) (0, (t : ℂ)) :=
      (analyticAt_const.sub analyticAt_snd).sub analyticAt_fst
    have harg : -(h false 0 (t : ℂ) / b 0) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      have hsub : -(h false 0 (t : ℂ) / b 0) = ((t - 1 : ℝ) : ℂ) := by
        simp only [h, b, Bool.false_eq_true, ite_false, sub_zero, div_one]
        push_cast
        ring
      rw [hsub, ofReal_re]
      exact sub_pos.mpr ht
    exact (hb.inv hb₀).mul (analyticAt_const.mul
      (((hh.div hb hb₀).neg).cpow analyticAt_const harg))
  · have hh : AnalyticAt ℂ (fun p : ℂ × ℂ => h true p.1 p.2) (0, (t : ℂ)) :=
      analyticAt_const.sub ((analyticAt_const.sub analyticAt_snd).mul analyticAt_fst)
    have harg : h true 0 (t : ℂ) / b 0 ∈ Complex.slitPlane := by simp [h, b]
    exact (hb.inv hb₀).mul ((hh.div hb hb₀).cpow analyticAt_const harg)

theorem dLipMean_eventuallyEq (upperA e : Bool) {r : ℂ} (hr : r ∈ dLip upperA) :
    (fun u => dLipMean upperA e u r) =ᶠ[𝓝 0] fun u => slitMean e u r := by
  cases e
  · let g (u : ℂ) := (h false u r / b u).im
    have hg : ContinuousAt g 0 :=
      Complex.continuous_im.continuousAt.comp
        ((by simp only [h, Bool.false_eq_true, ite_false]; fun_prop :
          ContinuousAt (fun u : ℂ => h false u r) 0).div
          (by unfold b; fun_prop) (by simp [b]))
    cases upperA
    · have hr' : 0 < r.im := hr
      have h₀ : g 0 < 0 := by simpa [g, h, b, sub_im] using neg_neg_of_pos hr'
      filter_upwards [hg.eventually_lt continuousAt_const h₀] with u hu
      simp only [dLipMean, Bool.false_eq_true, ite_false, phase, slitMean]
      rw [invHalfPower_lower hu]
    · have hr' : r.im < 0 := hr
      have h₀ : 0 < g 0 := by simpa [g, h, b, sub_im] using neg_pos.mpr hr'
      filter_upwards [continuousAt_const.eventually_lt hg h₀] with u hu
      simp only [dLipMean, Bool.false_eq_true, ite_false, phase, ite_true, slitMean]
      rw [invHalfPower_upper hu]
  · exact Eventually.of_forall (fun u => by simp [dLipMean])

private theorem dLipWeighted_false (upperA : Bool) {t : ℝ} (ht : 1 < t) :
    h false 0 (t : ℂ) * dLipMean upperA false 0 (t : ℂ) =
      (if upperA then I else -I) * (Real.sqrt (t - 1) : ℂ) := by
  have hpos : 0 < t - 1 := sub_pos.mpr ht
  have hn : ((t - 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  have he :
      ((t - 1 : ℝ) : ℂ) * ((t - 1 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) =
        (Real.sqrt (t - 1) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow hpos.le,
      ← show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [show (1 / 2 : ℂ) = 1 + (-1 / 2) by norm_num, cpow_add _ _ hn, cpow_one]
  have hsub : (1 : ℂ) - (t : ℂ) = -((t - 1 : ℝ) : ℂ) := by push_cast; ring
  cases upperA <;> simp only [h, b, sub_zero, Bool.false_eq_true, ite_false, ite_true,
    dLipMean, inv_one, one_mul, div_one, phase, hsub, neg_neg]
  · rw [← he]; ring
  · rw [← he]; ring

/-- The D-lip value of the regularizing denominator cannot vanish at the
Taylor centre. Equal signs give two equal terms. Mixed signs give real part one. -/
theorem dLipWeighted_sum_ne_zero (upperA e f : Bool) {t : ℝ} (ht : 1 < t) :
    h e 0 (t : ℂ) * dLipMean upperA e 0 (t : ℂ) +
      h f 0 (t : ℂ) * dLipMean upperA f 0 (t : ℂ) ≠ 0 := by
  have hf := dLipWeighted_false upperA ht
  have htrue : h true 0 (t : ℂ) * dLipMean upperA true 0 (t : ℂ) = 1 := by
    simp [h, b, dLipMean, slitMean]
  have hIm : ((if upperA then I else -I) *
      (Real.sqrt (t - 1) : ℂ)).re = 0 := by
    cases upperA <;> simp [mul_re]
  have hne : (if upperA then I else -I) *
      (Real.sqrt (t - 1) : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · cases upperA <;> simp
    · exact ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos (sub_pos.mpr ht)).ne'
  cases e <;> cases f
  · rw [hf, ← two_mul]
    exact mul_ne_zero (by norm_num) hne
  · rw [hf, htrue]
    intro hz
    have hr := congrArg Complex.re hz
    rw [add_re, hIm, one_re, zero_re] at hr
    norm_num at hr
  · rw [htrue, hf]
    intro hz
    have hr := congrArg Complex.re hz
    rw [add_re, hIm, one_re, zero_re] at hr
    norm_num at hr
  · rw [htrue]
    norm_num

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
