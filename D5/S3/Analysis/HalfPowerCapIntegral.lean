/- GID: D5/S3/Analysis/HalfPowerCapIntegral
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary5-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The half-power cap integral and its finite remainder after subtracting the logarithmic singularity. -/

import OmegaBuild.Commands
import D5.S3.Analysis.RightHalfPlaneLogIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

The half-power cap integral and its finite remainder after subtracting the
logarithmic singularity.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Omega

/-- Principal complex square root. -/
abbrev principalRoot (z : ℂ) : ℂ := z ^ (2⁻¹ : ℂ)

theorem principalRoot_sq (z : ℂ) : principalRoot z ^ (2 : ℕ) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [principalRoot]
  · rw [principalRoot, pow_two, ← cpow_add _ _ hz, show (2⁻¹ + 2⁻¹ : ℂ) = 1 by norm_num,
      cpow_one]

theorem principalRoot_norm (z : ℂ) : ‖principalRoot z‖ = Real.sqrt ‖z‖ := by
  rw [principalRoot, Real.sqrt_eq_rpow, ← Complex.norm_cpow_real]
  norm_num

theorem principalRoot_ofReal {t : ℝ} (ht : 0 ≤ t) :
    principalRoot (t : ℂ) = (Real.sqrt t : ℂ) := by
  rw [principalRoot, Real.sqrt_eq_rpow, Complex.ofReal_cpow ht]
  norm_num

theorem principalRoot_scale {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ≠ 0) :
    principalRoot ((a : ℂ) * z) = (Real.sqrt a : ℂ) * principalRoot z := by
  have ha' := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [principalRoot, cpow_def_of_ne_zero (mul_ne_zero ha' hz), log_ofReal_mul ha hz,
    add_mul, exp_add, Complex.ofReal_log ha.le, ← cpow_def_of_ne_zero ha',
    ← cpow_def_of_ne_zero hz]
  rw [show (a : ℂ) ^ (2⁻¹ : ℂ) = (Real.sqrt a : ℂ) from principalRoot_ofReal ha.le]

theorem principalRoot_re_pos {z : ℂ} (hz : 0 < z.re) : 0 < (principalRoot z).re := by
  have hslit : z ∈ slitPlane := Or.inl hz
  rw [principalRoot, cpow_def_of_ne_zero (slitPlane_ne_zero hslit), exp_re]
  apply mul_pos (Real.exp_pos _)
  have hi : (log z * (2⁻¹ : ℂ)).im = z.arg / 2 := by
    simp [Complex.mul_im, Complex.inv_re, Complex.inv_im, log_im]
    ring
  rw [hi]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [neg_pi_div_two_lt_arg_iff.2 (Or.inl hz),
    arg_lt_pi_div_two_iff.2 (Or.inl hz), Real.pi_pos]

theorem principalRoot_continuousAt {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt principalRoot z :=
  (differentiableAt_id.cpow_const (c := (2⁻¹ : ℂ)) (Or.inl hz)).continuousAt

/-- The cap kernel of a sphere with three angular dimensions. -/
def halfPowerCap (t : ℝ) (d : ℂ) : ℂ :=
  ((t : ℂ) + d)⁻¹ * (principalRoot ((t : ℂ) + d))⁻¹

theorem halfPowerCap_norm_le {t : ℝ} {d : ℂ} (ht : 0 < t) (hd : 0 ≤ d.re) :
    ‖halfPowerCap t d‖ ≤ (t * Real.sqrt t)⁻¹ := by
  have hb : t ≤ ‖(t : ℂ) + d‖ := by
    have h := re_le_norm ((t : ℂ) + d)
    rw [Complex.add_re, Complex.ofReal_re] at h
    linarith
  rw [halfPowerCap, norm_mul, norm_inv, norm_inv, principalRoot_norm, ← mul_inv]
  exact inv_anti₀ (by positivity) (mul_le_mul hb (Real.sqrt_le_sqrt hb) (by positivity)
    (norm_nonneg _))

theorem halfPowerCap_continuousAt {t : ℝ} {d : ℂ} (hd : 0 < t + d.re) :
    ContinuousAt (halfPowerCap t) d := by
  have hs : 0 < ((t : ℂ) + d).re := by simpa using hd
  have hne := slitPlane_ne_zero (Or.inl hs)
  have hr := (principalRoot_re_pos hs).ne'
  have hr' : principalRoot ((t : ℂ) + d) ≠ 0 := fun h => hr (by simp [h])
  exact ((continuousAt_const.add continuousAt_id).inv₀ hne).mul
    (((principalRoot_continuousAt hs).comp (continuousAt_const.add continuousAt_id)).inv₀ hr')

def halfPowerCapFinitePart (d : ℂ) (t : ℝ) : ℂ :=
  2 * (log (principalRoot ((t : ℂ) + d) + (Real.sqrt t : ℂ)) -
    (Real.sqrt t : ℂ) / principalRoot ((t : ℂ) + d))

private theorem log_principalRoot {d : ℂ} (hd : 0 < d.re) :
    log (principalRoot d) = log d * (2⁻¹ : ℂ) := by
  rw [principalRoot, cpow_def_of_ne_zero (slitPlane_ne_zero (Or.inl hd))]
  apply log_exp
  all_goals
    have he : (log d * (2⁻¹ : ℂ)).im = d.arg / 2 := by
      simp [Complex.mul_im, Complex.inv_re, Complex.inv_im, log_im]
      ring
    rw [he]
    linarith [neg_pi_lt_arg d, arg_le_pi d, Real.pi_pos]

/-- The unweighted half-power cap has an explicit logarithmic primitive. -/
theorem integral_halfPowerCap_sqrt {d : ℂ} (hd : 0 < d.re) :
    (∫ t in (0 : ℝ)..2, (Real.sqrt t : ℂ) * halfPowerCap t d) =
      halfPowerCapFinitePart d 2 - log d := by
  have hpos {t : ℝ} (ht : 0 ≤ t) : 0 < ((t : ℂ) + d).re := by
    simpa only [Complex.add_re, Complex.ofReal_re] using add_pos_of_nonneg_of_pos ht hd
  have hr {t : ℝ} (ht : 0 ≤ t) : principalRoot ((t : ℂ) + d) ≠ 0 := by
    exact fun h => (principalRoot_re_pos (hpos ht)).ne' (by simp [h])
  have hc : ContinuousOn (fun t : ℝ => principalRoot ((t : ℂ) + d)) (Icc 0 2) := by
    intro t ht
    have h : ContinuousAt (fun x : ℝ => (x : ℂ) + d) t :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    exact ((principalRoot_continuousAt (hpos ht.1)).comp (x := t) h).continuousWithinAt
  have hs : Continuous (fun t : ℝ => (Real.sqrt t : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_sqrt
  have hl : ContinuousOn (halfPowerCapFinitePart d) (Icc 0 2) := by
    unfold halfPowerCapFinitePart
    refine continuousOn_const.mul (((hc.add hs.continuousOn).clog ?_).sub
      (hs.continuousOn.div hc (fun _ ht => hr ht.1)))
    intro t ht
    apply Or.inl
    change 0 < (principalRoot ((t : ℂ) + d) + (Real.sqrt t : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg (principalRoot_re_pos (hpos ht.1)) (Real.sqrt_nonneg _)
  have hi : IntervalIntegrable (fun t : ℝ => (Real.sqrt t : ℂ) * halfPowerCap t d) volume 0 2 := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    unfold halfPowerCap
    refine hs.continuousOn.mul (((Complex.continuous_ofReal.add continuous_const).continuousOn.inv₀
      (fun t ht => slitPlane_ne_zero (Or.inl (hpos ht.1)))).mul (hc.inv₀ fun _ ht => hr ht.1))
  have hdiff (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 2) :
      HasDerivAt (halfPowerCapFinitePart d) ((Real.sqrt t : ℂ) * halfPowerCap t d) t := by
    let p := (Real.sqrt t : ℂ)
    let q := principalRoot ((t : ℂ) + d)
    have hp : p ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
    have hq : q ≠ 0 := hr ht.1.le
    have hpq : p + q ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      change (p + q).re = 0 at h'
      rw [Complex.add_re, show p.re = Real.sqrt t by simp [p]] at h'
      linarith [Real.sqrt_nonneg t, principalRoot_re_pos (hpos ht.1.le)]
    have hq2 : q ^ 2 = (t : ℂ) + d := principalRoot_sq _
    have hds : HasDerivAt (fun x : ℝ => (Real.sqrt x : ℂ)) (1 / (2 * p)) t := by
      have h := (Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x := Real.sqrt t)).scomp t
        (Real.hasDerivAt_sqrt ht.1.ne')
      change HasDerivAt (fun x : ℝ => (Real.sqrt x : ℂ))
        ((1 / (2 * Real.sqrt t)) • (1 : ℂ)) t at h
      simpa [p, Complex.real_smul] using h
    have hdz : HasDerivAt (fun x : ℝ => (x : ℂ) + d) 1 t :=
      Complex.ofRealCLM.hasFDerivAt.hasDerivAt.add_const d
    have hdq : HasDerivAt (fun x : ℝ => principalRoot ((x : ℂ) + d)) (1 / (2 * q)) t := by
      have h := (((hasDerivAt_id ((t : ℂ) + d)).cpow_const (c := (2⁻¹ : ℂ))
        (Or.inl (hpos ht.1.le))).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hdz
      have he : ((fun x : ℂ => id x ^ (2⁻¹ : ℂ)) ∘ fun x : ℝ => (x : ℂ) + d) =
          fun x : ℝ => principalRoot ((x : ℂ) + d) := rfl
      rw [he] at h
      convert h using 1
      change 1 / (2 * q) = (1 : ℂ) • (2⁻¹ * (((t : ℂ) + d) ^ (2⁻¹ - 1 : ℂ)) * 1)
      rw [one_smul, show (2⁻¹ - 1 : ℂ) = -(2⁻¹) by norm_num, cpow_neg]
      change _ = 2⁻¹ * q⁻¹ * 1
      ring
    have hslit : q + p ∈ slitPlane := Or.inl (by
      rw [Complex.add_re, show p.re = Real.sqrt t by simp [p]]
      exact add_pos_of_pos_of_nonneg (principalRoot_re_pos (hpos ht.1.le)) (Real.sqrt_nonneg _))
    have h := (((hdq.add hds).clog_real hslit).sub (hds.div hdq hq)).const_mul 2
    have h' : HasDerivAt (halfPowerCapFinitePart d)
        (2 * (((1 / (2 * q) + 1 / (2 * p)) / (q + p)) -
        ((1 / (2 * p)) * q - p * (1 / (2 * q))) / q ^ 2)) t := h
    convert h' using 1
    change p * (((t : ℂ) + d)⁻¹ * q⁻¹) =
      2 * (((1 / (2 * q) + 1 / (2 * p)) / (q + p)) -
        ((1 / (2 * p)) * q - p * (1 / (2 * q))) / q ^ 2)
    rw [← hq2]
    field_simp [hp, hq, add_comm q p ▸ hpq]
    <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hl hdiff hi]
  congr 1
  simp [halfPowerCapFinitePart, log_principalRoot hd]
  ring

/-- The finite part of the unweighted cap is continuous at zero. -/
theorem continuousAt_halfPowerCap_finitePart :
    ContinuousAt (fun d => halfPowerCapFinitePart d 2) 0 := by
  have hr : 0 < ((2 : ℂ) + 0).re := by norm_num
  have h := (principalRoot_continuousAt hr).comp
    (continuousAt_const.add continuousAt_id : ContinuousAt (fun d : ℂ => 2 + d) 0)
  have hn : principalRoot (2 + 0) ≠ 0 :=
    fun he => (principalRoot_re_pos hr).ne' (by rw [he]; rfl)
  have hs : principalRoot (2 + 0) + (Real.sqrt 2 : ℂ) ∈ slitPlane := Or.inl (by
    rw [Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg (principalRoot_re_pos hr) (Real.sqrt_nonneg _))
  exact continuousAt_const.mul (((h.add continuousAt_const).clog hs).sub
    (continuousAt_const.div h hn))

private def densityError (t : ℝ) : ℝ :=
  Real.sqrt t * (Real.sqrt (1 - t / 2) - 1)

private theorem densityError_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    ‖densityError t‖ ≤ Real.sqrt t * (t / 2) := by
  have h₀ : 0 ≤ 1 - t / 2 := by linarith [ht.2]
  have h₁ : Real.sqrt (1 - t / 2) ≤ 1 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    linarith [ht.1]
  have h₂ : 1 - t / 2 ≤ Real.sqrt (1 - t / 2) := by
    nlinarith [Real.sq_sqrt h₀, Real.sqrt_nonneg (1 - t / 2)]
  unfold densityError
  rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr h₁)]
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)

/-- The finite part of the cap integral with semicircle density. -/
def semicircleCapFinitePart (d : ℂ) : ℂ :=
  halfPowerCapFinitePart d 2 +
    ∫ t in Ioo (0 : ℝ) 2, (densityError t : ℂ) * halfPowerCap t d

theorem semicircleCapIntegral_eq {d : ℂ} (hd : 0 < d.re) :
    (∫ t in (0 : ℝ)..2, (Real.sqrt t * Real.sqrt (1 - t / 2) : ℝ) *
      halfPowerCap t d) = semicircleCapFinitePart d - log d := by
  have hc : ContinuousOn (fun t : ℝ => halfPowerCap t d) (uIcc 0 2) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    have ht' : 0 < ((t : ℂ) + d).re := by
      simpa using add_pos_of_nonneg_of_pos ht.1 hd
    have h : ContinuousAt (fun t : ℝ => (t : ℂ) + d) t :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    have hr := (principalRoot_continuousAt ht').comp (x := t) h
    exact ((h.inv₀ (slitPlane_ne_zero (Or.inl ht'))).mul
      (hr.inv₀ (fun he => (principalRoot_re_pos ht').ne' (by
        change principalRoot ((t : ℂ) + d) = 0 at he
        rw [he]; rfl)))).continuousWithinAt
  have h₁ : IntervalIntegrable (fun t : ℝ => (Real.sqrt t : ℂ) * halfPowerCap t d) volume 0 2 :=
    ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.mul hc).intervalIntegrable
  have h₂ : IntervalIntegrable (fun t : ℝ => (densityError t : ℂ) * halfPowerCap t d) volume 0 2 := by
    apply ContinuousOn.intervalIntegrable
    refine (Continuous.continuousOn ?_).mul hc
    unfold densityError
    fun_prop
  have he (t : ℝ) : (Real.sqrt t * Real.sqrt (1 - t / 2) : ℝ) * halfPowerCap t d =
      (Real.sqrt t : ℂ) * halfPowerCap t d + (densityError t : ℂ) * halfPowerCap t d := by
    push_cast [densityError]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_add h₁ h₂, integral_halfPowerCap_sqrt hd,
    intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
  unfold semicircleCapFinitePart
  ring

theorem tendsto_semicircleCapFinitePart :
    Tendsto semicircleCapFinitePart (𝓝[{d : ℂ | 0 ≤ d.re}] 0)
      (𝓝 (semicircleCapFinitePart 0)) := by
  unfold semicircleCapFinitePart
  refine (continuousAt_halfPowerCap_finitePart.tendsto.mono_left nhdsWithin_le_nhds).add ?_
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => 1 / 2)
  · refine .of_forall fun d => Measurable.aestronglyMeasurable ?_
    unfold densityError halfPowerCap principalRoot
    fun_prop
  · filter_upwards [self_mem_nhdsWithin] with d hd
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht
    rw [norm_mul, Complex.norm_real]
    have h := mul_le_mul (densityError_bound ⟨ht.1.le, ht.2.le⟩)
      (halfPowerCap_norm_le ht.1 hd) (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg ht.1.le (by norm_num)))
    refine h.trans_eq ?_
    field_simp [ht.1.ne', (Real.sqrt_pos.2 ht.1).ne']
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht
    exact ((halfPowerCap_continuousAt (d := 0) (by simpa using ht.1)).tendsto.const_mul
      (densityError t : ℂ)).mono_left nhdsWithin_le_nhds

end Omega
