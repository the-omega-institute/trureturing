/- GID: D5/S3/Calculus/ClausenLocalGerms
   generality: G
   mirror-B: none(waiver:covered-by-phase-resummation-log-germ-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The smooth log-sinc primitive and the two cubic functions in the local Clausen expansion. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Omega original.

The smooth log-sinc primitive and the two cubic functions in the local Clausen expansion.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace Omega.Calculus.ClausenLocalGerms

private def U : Set ℝ := Ioo (-Real.pi) Real.pi

private lemma mem_U {g : ℝ} : g ∈ U ↔ |g| < Real.pi := abs_lt.symm

private lemma zero_mem_U : (0 : ℝ) ∈ U := mem_U.2 (by simp [Real.pi_pos])

/-- The logarithm of the normalized sine. -/
def sincLog (g : ℝ) : ℝ := Real.log (Real.sinc g)

/-- The primitive of the logarithm of sinc, normalized at zero. -/
def primitive (g : ℝ) : ℝ := ∫ t in 0..g, sincLog t

private lemma contDiffOn_sincLog : ContDiffOn ℝ ∞ sincLog U := by
  refine ContDiffOn.log (fun x _ => ?_) (fun x hx => (Real.sinc_pos (mem_U.1 hx)).ne')
  by_cases h : x = 0
  · subst x
    rw [Real.sinc_eq_dslope]
    obtain ⟨p, hp⟩ := Real.analyticAt_sin (x := 0)
    exact hp.has_fpower_series_dslope_fslope.analyticAt.contDiffAt.contDiffWithinAt
  · have hd := Real.contDiff_sin.contDiffAt.div contDiffAt_id h (n := ∞)
    apply (hd.congr_of_eventuallyEq ?_).contDiffWithinAt
    exact (eventually_ne_nhds h).mono fun t ht => Real.sinc_of_ne_zero ht

/-- The logarithm of sinc is integrable on segments from zero within the first lobe. -/
theorem intervalIntegrable_sincLog {g : ℝ} (hg : g ∈ Ioo (-Real.pi) Real.pi) :
    IntervalIntegrable sincLog volume 0 g := by
  exact (contDiffOn_sincLog.continuousOn.mono
    (ordConnected_Ioo.uIcc_subset zero_mem_U hg)).intervalIntegrable

private lemma hasDerivAt_J {g : ℝ} (hg : g ∈ U) : HasDerivAt primitive (sincLog g) g := by
  exact intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_sincLog hg)
    ((Real.measurable_log.comp Real.continuous_sinc.measurable).stronglyMeasurable.stronglyMeasurableAtFilter)
    (contDiffOn_sincLog.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hg))

/-- The normalized primitive is smooth on the first lobe. -/
theorem contDiffOn_primitive : ContDiffOn ℝ ∞ primitive (Ioo (-Real.pi) Real.pi) := by
  refine (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo).2
    ⟨fun t ht => (hasDerivAt_J ht).differentiableAt.differentiableWithinAt, ?_⟩
  exact contDiffOn_sincLog.congr fun t ht => (hasDerivAt_J ht).deriv

/-- The primitive of the even log-sinc kernel is odd. -/
theorem primitive_neg (g : ℝ) : primitive (-g) = -primitive g := by
  unfold primitive
  rw [intervalIntegral.integral_symm]
  have heq := intervalIntegral.integral_comp_neg (f := sincLog) (a := (0 : ℝ)) (b := g)
  simpa [sincLog] using congrArg Neg.neg heq.symm

/-- A quadratic bound for the log-sinc kernel near zero. -/
theorem sincLog_bound {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    |sincLog t| ≤ t ^ 2 / 5 := by
  rcases ht₀.eq_or_lt with rfl | ht₀
  · simp [sincLog]
  have hlo : 1 - t ^ 2 / 6 ≤ Real.sinc t := by
    rw [Real.sinc_of_ne_zero ht₀.ne', le_div_iff₀ ht₀]
    have h := (le_abs_self (t - Real.sin t)).trans (Real.abs_sub_sin_le t)
    rw [abs_of_pos ht₀] at h
    linarith
  have ht : t ^ 2 ≤ 1 := by nlinarith
  have h56 : 5 / 6 ≤ Real.sinc t := by linarith
  have hpos : 0 < Real.sinc t := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hlog
  unfold sincLog
  rw [abs_of_nonpos (Real.log_nonpos hpos.le (Real.sinc_le_one t))]
  apply hlog.trans
  rw [← one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
  nlinarith [mul_nonneg (show 0 ≤ Real.sinc t - 5 / 6 by linarith) (sq_nonneg t)]

private lemma zero_slope {f k : ℝ → ℝ} (hk : ContinuousAt k 0) (h : ∀ x, f x = x * k x) :
    HasDerivAt f (k 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply (hk.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ)] with x hx
  rw [slope_def_field, h x, h 0, zero_mul, sub_zero, sub_zero, mul_div_cancel_left₀ _ hx]

/-- The cubic logarithmic function with the total real logarithm. -/
def logCubic (x : ℝ) : ℝ := x ^ 3 * Real.log x

/-- The first derivative of the cubic logarithmic function. -/
def logCubicD (x : ℝ) : ℝ := x ^ 2 * (3 * Real.log x + 1)

/-- The second derivative of the cubic logarithmic function. -/
def logCubicDD (x : ℝ) : ℝ := x * (6 * Real.log x + 5)

/-- The first derivative formula holds on the full real line. -/
theorem logCubic_hasDerivAt (x : ℝ) : HasDerivAt logCubic (logCubicD x) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [logCubicD] using (zero_slope (k := fun t => t * (t * Real.log t))
      (continuous_id.mul Real.continuous_mul_log).continuousAt (by intro t; unfold logCubic; ring))
  · refine (((hasDerivAt_id x).pow 3).mul (Real.hasDerivAt_log hx)).congr_deriv ?_
    dsimp [logCubicD, id]
    field_simp [hx]

/-- The second derivative formula includes the origin. -/
theorem logCubicD_hasDerivAt (x : ℝ) : HasDerivAt logCubicD (logCubicDD x) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simpa [logCubicDD] using (zero_slope (k := fun t => 3 * (t * Real.log t) + t)
      ((Real.continuous_mul_log.const_mul 3).add continuous_id).continuousAt
      (by intro t; unfold logCubicD; ring))
  · refine (((hasDerivAt_id x).pow 2).mul
      (((Real.hasDerivAt_log hx).const_mul 3).add_const 1)).congr_deriv ?_
    dsimp [logCubicDD, id]
    field_simp [hx]
    ring

private lemma contDiff_two_of_derivs {f f' f'' : ℝ → ℝ}
    (h₁ : ∀ x, HasDerivAt f (f' x) x) (h₂ : ∀ x, HasDerivAt f' (f'' x) x)
    (h₃ : Continuous f'') : ContDiff ℝ 2 f := by
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (h₁ x).differentiableAt, by simp, ?_⟩
  rw [funext fun x => (h₁ x).deriv, contDiff_one_iff_deriv, funext fun x => (h₂ x).deriv]
  exact ⟨fun x => (h₂ x).differentiableAt, h₃⟩

/-- The cubic logarithmic function has a continuous second derivative. -/
theorem contDiff_logCubic : ContDiff ℝ 2 logCubic :=
  contDiff_two_of_derivs logCubic_hasDerivAt logCubicD_hasDerivAt (by
    convert (Real.continuous_mul_log.const_mul 6).add (continuous_id.const_mul 5) using 1
    ext x
    unfold logCubicDD
    dsimp [id]
    ring)

/-- The derivative of the cubed absolute value. -/
theorem absCube_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => |t| ^ 3) (3 * (x * |x|)) x := by
  convert hasDerivAt_abs_rpow x (p := 3) (by norm_num) using 1
  · ext t
    exact (Real.rpow_natCast |t| 3).symm
  · norm_num
    ring

/-- The signed square has derivative twice the absolute value. -/
theorem mulAbs_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t : ℝ => t * |t|) (2 * |x|) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · refine ((hasDerivAt_id x).mul (hasDerivAt_abs_neg hx)).congr_deriv ?_
    simp [abs_of_neg hx, id, two_mul]
  · simpa using (zero_slope (f := fun t => t * |t|) continuous_abs.continuousAt fun _ => rfl)
  · refine ((hasDerivAt_id x).mul (hasDerivAt_abs_pos hx)).congr_deriv ?_
    simp [abs_of_pos hx, id, two_mul]

/-- The cubed absolute value is twice continuously differentiable. -/
theorem contDiff_absCube : ContDiff ℝ 2 (fun t : ℝ => |t| ^ 3) :=
  contDiff_two_of_derivs absCube_hasDerivAt (fun x => (mulAbs_hasDerivAt x).const_mul 3)
    (by fun_prop)

/-- The second derivative has a logarithmically divergent slope on the right. -/
theorem logCubicDD_not_differentiable : ¬ DifferentiableAt ℝ logCubicDD 0 := by
  intro hd
  have hfinite := hd.hasDerivAt.tendsto_slope.mono_left
    (nhdsWithin_mono (0 : ℝ) (fun _ h => ne_of_gt h : Ioi 0 ⊆ ({0} : Set ℝ)ᶜ))
  apply not_tendsto_atBot_of_tendsto_nhds hfinite
  have hlog := (Real.tendsto_log_nhdsGT_zero.atBot_mul_const (show (0 : ℝ) < 6 by norm_num))
    |>.atBot_add (tendsto_const_nhds (x := (5 : ℝ)))
  apply hlog.congr'
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with g hg
  rw [slope_def_field, logCubicDD, logCubicDD, zero_mul, sub_zero, sub_zero,
    mul_div_cancel_left₀ _ (ne_of_gt hg), mul_comm (Real.log g)]

end Omega.Calculus.ClausenLocalGerms
