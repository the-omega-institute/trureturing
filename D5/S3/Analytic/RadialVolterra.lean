/- GID: D5/S3/Analytic/RadialVolterra
   generality: I
   mirror-B: D5/B/S3/Analytic/RadialVolterra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform bounds for a complex scalar Volterra system on the positive half-line. -/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Filter Set Topology MeasureTheory

namespace D5.S3.Analytic.RadialVolterra

/-- Finite interval mass control and terminal data give uniform bounds for the scalar system. -/
theorem norm_bounds
    {ν V : ℝ} (hV : 0 ≤ V) (hνV : V < ν)
    {η F G p q : ℝ → ℂ} {Q : ℝ → ℝ}
    (hp : ContinuousOn p (Ioi 0)) (hq : ContinuousOn q (Ioi 0))
    (hη : ∀ x > 0, HasDerivAt η (p x) x)
    (hF : ∀ x > 0, HasDerivAt F (p x * G x) x)
    (hG : ∀ x > 0, HasDerivAt G (2 * (ν : ℂ) * p x * G x + q x * F x) x)
    (hphase : ∀ x > 0, 0 ≤ (p x).re)
    (hFinfty : Tendsto F atTop (𝓝 1)) (hGinfty : Tendsto G atTop (𝓝 0))
    (hQ : ContinuousOn Q (Ioi 0)) (hQ0 : ∀ x > 0, 0 ≤ Q x)
    (hqQ : ∀ x > 0, ‖q x‖ ≤ Q x)
    (hmass : ∀ a b : ℝ, 0 < a → a ≤ b → (∫ x in a..b, Q x) ≤ V) :
    ∀ r > 0, ‖F r‖ ≤ ν / (ν - V) ∧ ‖F r - 1‖ ≤ V / (ν - V) := by
  have hν := hV.trans_lt hνV
  have hgap : 0 < ν - V := sub_pos.mpr hνV
  have hηre (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun t => (η t).re) (p x).re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt (hη x hx)
  have hmonotone : MonotoneOn (fun t => (η t).re) (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun x hx => (hηre x hx).continuousAt.continuousWithinAt
    · rw [isOpen_Ioi.interior_eq]
      exact fun x hx => (hηre x hx).differentiableAt.differentiableWithinAt
    · rw [isOpen_Ioi.interior_eq]
      intro x hx
      rw [(hηre x hx).deriv]
      exact hphase x hx
  have hFcont : ContinuousOn F (Ioi 0) :=
    fun x hx => (hF x hx).continuousAt.continuousWithinAt
  intro a ha
  let values := (fun x => ‖F x‖) '' Ici a
  let M := sSup values
  have hvalues : BddAbove values := by
    have hnorm : Tendsto (fun x => ‖F x‖) atTop (𝓝 (1 : ℝ)) := by
      simpa using hFinfty.norm
    obtain ⟨b, hb⟩ := eventually_atTop.mp
      (hnorm.eventually_lt_const (show (1 : ℝ) < 2 by norm_num))
    have hsubset : Icc a b ⊆ Ioi (0 : ℝ) := fun _ hx => ha.trans_le hx.1
    obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hFcont.norm.mono hsubset)
    refine ⟨max B 2, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    by_cases hbx : b ≤ x
    · exact (hb x hbx).le.trans (le_max_right _ _)
    · exact (hB (mem_image_of_mem _ ⟨hx, le_of_not_ge hbx⟩)).trans (le_max_left _ _)
  have hM (x : ℝ) (hx : a ≤ x) : ‖F x‖ ≤ M :=
    le_csSup hvalues (mem_image_of_mem _ hx)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a le_rfl)
  have herror (r : ℝ) (har : a ≤ r) : ‖F r - 1‖ ≤ M * V / ν := by
    have hr := ha.trans_le har
    let c : ℂ := 2 * (ν : ℂ)
    have hc : c ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast hν.ne')
    let E (s : ℝ) := Complex.exp (-c * (η s - η r))
    let k (s : ℝ) := (1 - E s) / c
    let H (s : ℝ) := F s - k s * G s
    have hE (s : ℝ) (hs : 0 < s) :
        HasDerivAt E ((-c * p s) * E s) s := by
      have harg := ((hη s hs).sub_const (η r)).const_mul (-c)
      exact (Complex.hasDerivAt_exp (-c * (η s - η r))).scomp harg
    have hk (s : ℝ) (hs : 0 < s) : HasDerivAt k (p s * E s) s := by
      have hd := ((hE s hs).const_sub 1).div_const c
      convert hd using 1
      field_simp [hc]
    have hH (s : ℝ) (hs : 0 < s) : HasDerivAt H (-k s * q s * F s) s := by
      have hd := (hF s hs).sub ((hk s hs).mul (hG s hs))
      change HasDerivAt G (c * p s * G s + q s * F s) s at *
      have hcancel : k s * c = 1 - E s := div_mul_cancel₀ _ hc
      convert hd using 1
      linear_combination -(p s * G s) * hcancel
    have hHr : H r = F r := by simp [H, k, E]
    have hknorm (s : ℝ) (hrs : r ≤ s) : ‖k s‖ ≤ 1 / ν := by
      have hphase_le := hmonotone hr (hr.trans_le hrs) hrs
      have hEbound : ‖E s‖ ≤ 1 := by
        rw [E, Complex.norm_exp, Real.exp_le_one_iff]
        have hreal : (-c * (η s - η r)).re = -(2 * ν) * ((η s).re - (η r).re) := by
          simp [c, Complex.mul_re]
        rw [hreal]
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hphase_le)
      have hcnorm : ‖c‖ = 2 * ν := by
        simp [c, norm_mul, Complex.norm_ofReal, abs_of_pos hν]
      calc
        ‖k s‖ = ‖1 - E s‖ / (2 * ν) := by rw [k, norm_div, hcnorm]
        _ ≤ 2 / (2 * ν) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact (norm_sub_le _ _).trans (by simpa using add_le_add_left hEbound (1 : ℝ))
        _ = 1 / ν := by ring
    have hHlim : Tendsto H atTop (𝓝 1) := by
      have hkbounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ k) :=
        ⟨1 / ν, (eventually_ge_atTop r).mono fun s hs => hknorm s hs⟩
      simpa only [sub_zero] using hFinfty.sub (hkbounded.isBoundedUnder_le_mul_tendsto_zero hGinfty)
    have hfinite (R : ℝ) (hrR : r ≤ R) : ‖H R - F r‖ ≤ M * V / ν := by
      let integrand (s : ℝ) := -k s * q s * F s
      have hpositive : [[r, R]] ⊆ Ioi (0 : ℝ) := by
        rw [uIcc_of_le hrR]
        exact fun _ hs => hr.trans_le hs.1
      have hkcont : ContinuousOn k (Ioi 0) :=
        fun x hx => (hk x hx).continuousAt.continuousWithinAt
      have hcont : ContinuousOn integrand [[r, R]] :=
        ((hkcont.neg.mul hq).mul hFcont).mono hpositive
      have hFTC : (∫ s in r..R, integrand s) = H R - F r := by
        rw [← hHr]
        exact intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun s hs => hH s (hpositive hs)) hcont.intervalIntegrable
      have hmajorant : ContinuousOn (fun s => ((1 / ν) * M) * Q s) [[r, R]] :=
        continuousOn_const.mul (hQ.mono hpositive)
      rw [← hFTC]
      calc
        ‖∫ s in r..R, integrand s‖ ≤ ∫ s in r..R, ‖integrand s‖ :=
          intervalIntegral.norm_integral_le_integral_norm hrR
        _ ≤ ∫ s in r..R, ((1 / ν) * M) * Q s := by
          apply intervalIntegral.integral_mono_on hrR
            hcont.norm.intervalIntegrable hmajorant.intervalIntegrable
          intro s hs
          have hs0 := hr.trans_le hs.1
          calc
            ‖integrand s‖ = ‖k s‖ * ‖q s‖ * ‖F s‖ := by simp [integrand, norm_mul]
            _ ≤ (1 / ν) * Q s * M := by
              exact mul_le_mul
                (mul_le_mul (hknorm s hs.1) (hqQ s hs0) (norm_nonneg _) (by positivity))
                (hM s (har.trans hs.1)) (norm_nonneg _) (by positivity)
            _ = ((1 / ν) * M) * Q s := by ring
        _ = ((1 / ν) * M) * (∫ s in r..R, Q s) := intervalIntegral.integral_const_mul ..
        _ ≤ ((1 / ν) * M) * V :=
          mul_le_mul_of_nonneg_left (hmass r R hr hrR) (by positivity)
        _ = M * V / ν := by ring
    rw [norm_sub_rev]
    exact le_of_tendsto ((hHlim.sub tendsto_const_nhds).norm)
      ((eventually_ge_atTop r).mono fun R hR => hfinite R hR)
  have hMsup : M ≤ 1 + M * V / ν := by
    apply csSup_le ⟨‖F a‖, mem_image_of_mem _ le_rfl⟩
    rintro _ ⟨r, hr, rfl⟩
    calc
      ‖F r‖ = ‖1 + (F r - 1)‖ := by rw [add_comm, sub_add_cancel]
      _ ≤ ‖(1 : ℂ)‖ + ‖F r - 1‖ := norm_add_le _ _
      _ ≤ 1 + M * V / ν := by rw [norm_one]; exact add_le_add_left (herror r hr) _
  have hMbound : M ≤ ν / (ν - V) := by
    apply (le_div_iff₀ hgap).mpr
    have hscaled := mul_le_mul_of_nonneg_right hMsup hν.le
    rw [add_mul, one_mul, div_mul_cancel₀ _ hν.ne'] at hscaled
    linarith only [hscaled, mul_sub M ν V]
  refine ⟨(hM a le_rfl).trans hMbound, (herror a le_rfl).trans ?_⟩
  calc
    M * V / ν ≤ (ν / (ν - V)) * V / ν :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hMbound hV) hν.le
    _ = V / (ν - V) := by field_simp

end D5.S3.Analytic.RadialVolterra
