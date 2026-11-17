/- GID: D5/S3/Analytic/Asymptotics/PositiveSubexponentialRatio
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/PositiveSubexponentialRatio
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real-tail convergence excludes a nonzero linear exponential factor. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.Basic

open Filter
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio

/-- An exponential times an eventually positive ratio with sublinear logarithms
can converge to one on the full real tail only if its linear exponent vanishes. -/
theorem linear_exponent_eq_zero
    (a b : ℂ) (p q : ℝ → ℝ)
    (hp : ∀ᶠ x : ℝ in atTop, 0 < p x)
    (hq : ∀ᶠ x : ℝ in atTop, 0 < q x)
    (hlogp : Tendsto (fun x : ℝ => Real.log (p x) / x) atTop (𝓝 0))
    (hlogq : Tendsto (fun x : ℝ => Real.log (q x) / x) atTop (𝓝 0))
    (hlim : Tendsto
      (fun x : ℝ => Complex.exp (a * (x : ℂ) + b) * (p x : ℂ) / (q x : ℂ))
      atTop (𝓝 1)) :
    a = 0 := by
  let R : ℝ → ℂ := fun x =>
    Complex.exp (a * (x : ℂ) + b) * (p x : ℂ) / (q x : ℂ)
  have hR : Tendsto R atTop (𝓝 1) := hlim
  have hnorm : Tendsto (fun x => ‖R x‖) atTop (𝓝 (1 : ℝ)) := by
    simpa only [norm_one] using hR.norm
  have hnorm_eq : ∀ᶠ x : ℝ in atTop,
      ‖R x‖ = Real.exp (a.re * x + b.re) * p x / q x := by
    filter_upwards [hp, hq] with x hx hy
    simp only [R, norm_div, norm_mul, Complex.norm_exp,
      Complex.norm_of_nonneg hx.le, Complex.norm_of_nonneg hy.le,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
  have hlog_eq : ∀ᶠ x : ℝ in atTop,
      Real.log ‖R x‖ = a.re * x + b.re + Real.log (p x) - Real.log (q x) := by
    filter_upwards [hnorm_eq, hp, hq] with x hn hx hy
    rw [hn, Real.log_div (mul_ne_zero (Real.exp_ne_zero _) hx.ne') hy.ne',
      Real.log_mul (Real.exp_ne_zero _) hx.ne', Real.log_exp]
  have hlog : Tendsto (fun x => Real.log ‖R x‖) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp hnorm
  have hscaled : Tendsto (fun x : ℝ => Real.log ‖R x‖ / x) atTop (𝓝 0) :=
    hlog.div_atTop tendsto_id
  have hb : Tendsto (fun x : ℝ => b.re / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlinear : Tendsto
      (fun x : ℝ => a.re + b.re / x + Real.log (p x) / x - Real.log (q x) / x)
      atTop (𝓝 a.re) := by
    simpa only [add_zero, sub_zero] using
      (((tendsto_const_nhds : Tendsto (fun _ : ℝ => a.re) atTop (𝓝 a.re)).add hb).add
        hlogp).sub hlogq
  have hscaled_eq : (fun x : ℝ => Real.log ‖R x‖ / x) =ᶠ[atTop]
      (fun x : ℝ => a.re + b.re / x + Real.log (p x) / x - Real.log (q x) / x) := by
    filter_upwards [hlog_eq, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    rw [hx]
    field_simp [ne_of_gt hxpos] <;> ring
  have hre : a.re = 0 :=
    tendsto_nhds_unique hlinear (hscaled.congr' hscaled_eq)
  have hnormC : Tendsto (fun x => (‖R x‖ : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one, Function.comp_def] using
      (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hnorm
  have hnormalized : Tendsto (fun x => R x / (‖R x‖ : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    convert hR.div hnormC (one_ne_zero : (1 : ℂ) ≠ 0) using 1 <;> simp
  let phase : ℝ → ℂ := fun x =>
    Complex.exp (((a.im * x + b.im : ℝ) : ℂ) * Complex.I)
  have hphase_eq : (fun x => R x / (‖R x‖ : ℂ)) =ᶠ[atTop] phase := by
    filter_upwards [hnorm_eq, hp, hq] with x hn hx hy
    have hpC : (p x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hqC : (q x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    change R x / (‖R x‖ : ℂ) =
      Complex.exp (((a.im * x + b.im : ℝ) : ℂ) * Complex.I)
    rw [hn, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_exp]
    dsimp only [R]
    calc
      _ = Complex.exp (a * (x : ℂ) + b) /
          Complex.exp ((a.re * x + b.re : ℝ) : ℂ) := by
        field_simp [hpC, hqC, Complex.exp_ne_zero] <;> ring
      _ = Complex.exp ((a * (x : ℂ) + b) - ((a.re * x + b.re : ℝ) : ℂ)) :=
        (Complex.exp_sub _ _).symm
      _ = Complex.exp (((a.im * x + b.im : ℝ) : ℂ) * Complex.I) := by
        congr 1
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hphase : Tendsto phase atTop (𝓝 (1 : ℂ)) :=
    hnormalized.congr' hphase_eq
  -- Every real translation preserves this limit on the full real tail.
  have hcharacter (h : ℝ) : Complex.exp (((a.im * h : ℝ) : ℂ) * Complex.I) = 1 := by
    have hshift : Tendsto (fun x : ℝ => phase (x + h)) atTop (𝓝 (1 : ℂ)) :=
      hphase.comp (tendsto_atTop_add_const_right atTop h tendsto_id)
    have hmul : Tendsto
        (fun x => phase x * Complex.exp (((a.im * h : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 (Complex.exp (((a.im * h : ℝ) : ℂ) * Complex.I))) := by
      simpa only [one_mul] using
        hphase.mul_const (Complex.exp (((a.im * h : ℝ) : ℂ) * Complex.I))
    have htranslate :
        (fun x => phase x * Complex.exp (((a.im * h : ℝ) : ℂ) * Complex.I)) =ᶠ[atTop]
        (fun x => phase (x + h)) := by
      filter_upwards [] with x
      dsimp only [phase]
      rw [← Complex.exp_add]
      congr 1
      simp only [Complex.ofReal_add, Complex.ofReal_mul]
      ring
    exact tendsto_nhds_unique (hmul.congr' htranslate) hshift
  have him : a.im = 0 := by
    by_contra ha
    have h := hcharacter (Real.pi / a.im)
    have hpi : a.im * (Real.pi / a.im) = Real.pi := by
      field_simp [ha] <;> ring
    rw [hpi, Complex.exp_pi_mul_I] at h
    norm_num at h
  exact Complex.ext hre him

end D5.S3.Analytic.Asymptotics.PositiveSubexponentialRatio
