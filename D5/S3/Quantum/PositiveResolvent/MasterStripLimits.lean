/- GID: D5/S3/Quantum/PositiveResolvent/MasterStripLimits
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrability and boundary limits for the logarithmic master strip. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic
import D5.S3.Quantum.PositiveResolvent.MasterStripPoles

open MeasureTheory Filter Complex Set
open scoped Topology Interval

namespace D5.S3.Quantum.PositiveResolvent.MasterStripLimits

open D5.S3.Quantum.PositiveResolvent.MasterStripPoles

noncomputable def stripWeight (x s : ℝ) : ℝ :=
  Real.exp s / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2))

private lemma lorentz_rescale (s : ℝ) :
    1 / (s ^ 2 + Real.pi ^ 2) =
      (Real.pi ^ 2)⁻¹ * (1 + (s / Real.pi) ^ 2)⁻¹ := by
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem lorentz_integrable : Integrable (fun s : ℝ => 1 / (s ^ 2 + Real.pi ^ 2)) := by
  simp_rw [lorentz_rescale]
  exact (integrable_inv_one_add_sq.comp_div Real.pi_ne_zero).const_mul _

theorem lorentz_integral : (∫ s : ℝ, 1 / (s ^ 2 + Real.pi ^ 2)) = 1 := by
  simp_rw [lorentz_rescale]
  rw [integral_const_mul, Measure.integral_comp_div (fun s : ℝ => (1 + s ^ 2)⁻¹) Real.pi,
    integral_univ_inv_one_add_sq,
    abs_of_pos Real.pi_pos, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

theorem stripWeight_integrable (x : ℝ) (hx : 0 < x) : Integrable (stripWeight x) := by
  have hc : Continuous (stripWeight x) := by
    unfold stripWeight
    exact Real.continuous_exp.div
      ((continuous_const.add Real.continuous_exp).mul
        ((continuous_id.pow 2).add continuous_const))
      (fun s => ne_of_gt (by positivity))
  refine lorentz_integrable.mono' hc.aestronglyMeasurable (Eventually.of_forall ?_)
  intro s
  have hd : 0 < s ^ 2 + Real.pi ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold stripWeight; positivity)]
  unfold stripWeight
  apply (div_le_div_iff₀ (mul_pos (by positivity) hd) hd).2
  nlinarith [Real.exp_pos s]

private lemma reciprocalStrip_integrable (x : ℝ) (hx : 0 < x) :
    Integrable (fun s : ℝ => 1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2))) := by
  have hc : Continuous (fun s : ℝ => 1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2))) := by
    exact continuous_const.div
      ((continuous_const.add Real.continuous_exp).mul
        ((continuous_id.pow 2).add continuous_const))
      (fun s => ne_of_gt (by positivity))
  refine (lorentz_integrable.const_mul (1 / x)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall ?_)
  intro s
  have hd : 0 < s ^ 2 + Real.pi ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_mul_div_comm]
  simpa only [one_mul] using one_div_le_one_div_of_le (mul_pos hx hd)
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_pos s).le) hd.le)

private lemma strip_den_norm_lower (x T y : ℝ) (hx : 0 < x)
    (he : Real.exp T ≤ x / 2 ∨ 3 * x / 2 ≤ Real.exp T) :
    x / 2 ≤ ‖(x : ℂ) + Complex.exp ((T : ℂ) + (y : ℂ) * I)‖ := by
  have hn : ‖Complex.exp ((T : ℂ) + (y : ℂ) * I)‖ = Real.exp T := by
    simp [Complex.norm_exp]
  have hxnorm : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hx]
  rcases he with he | he
  · have h := norm_sub_norm_le (x : ℂ) (-Complex.exp ((T : ℂ) + (y : ℂ) * I))
    simp only [norm_neg, sub_neg_eq_add, hn, hxnorm] at h
    linarith
  · have h := norm_sub_norm_le (Complex.exp ((T : ℂ) + (y : ℂ) * I)) (-(x : ℂ))
    simp only [norm_neg, sub_neg_eq_add, hn, hxnorm] at h
    rw [add_comm] at h
    linarith

private lemma strip_axis_norm_lower (T y : ℝ) :
    |T| ≤ ‖(T : ℂ) + (y : ℂ) * I - (Real.pi : ℂ) * I‖ := by
  simpa using Complex.abs_re_le_norm ((T : ℂ) + (y : ℂ) * I - (Real.pi : ℂ) * I)

private lemma vertical_kernel_bound (x T y : ℝ) (hx : 0 < x) (hT : T ≠ 0)
    (he : Real.exp T ≤ x / 2 ∨ 3 * x / 2 ≤ Real.exp T) :
    ‖1 / (((x : ℂ) + Complex.exp ((T : ℂ) + (y : ℂ) * I)) *
      ((T : ℂ) + (y : ℂ) * I - (Real.pi : ℂ) * I))‖ ≤ 2 / (x * |T|) := by
  have hd := strip_den_norm_lower x T y hx he
  have ha := strip_axis_norm_lower T y
  rw [norm_div, norm_one, norm_mul]
  calc
    1 / (‖(x : ℂ) + Complex.exp ((T : ℂ) + (y : ℂ) * I)‖ *
        ‖(T : ℂ) + (y : ℂ) * I - (Real.pi : ℂ) * I‖) ≤
        1 / ((x / 2) * |T|) :=
      one_div_le_one_div_of_le (mul_pos (by positivity) (abs_pos.mpr hT))
        (mul_le_mul hd ha (abs_nonneg _) (norm_nonneg _))
    _ = 2 / (x * |T|) := by ring

private lemma vertical_integral_bound (x T : ℝ) (hx : 0 < x) (hT : T ≠ 0)
    (he : Real.exp T ≤ x / 2 ∨ 3 * x / 2 ≤ Real.exp T) :
    ‖∫ y in (0 : ℝ)..2 * Real.pi,
      1 / (((x : ℂ) + Complex.exp ((T : ℂ) + (y : ℂ) * I)) *
      ((T : ℂ) + (y : ℂ) * I - (Real.pi : ℂ) * I))‖ ≤
      (2 / (x * |T|)) * (2 * Real.pi) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (fun y _ => vertical_kernel_bound x T y hx hT he)
  simpa [abs_mul, abs_of_pos Real.pi_pos] using h

theorem vertical_right_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => ∫ y in (0 : ℝ)..2 * Real.pi,
      1 / (((x : ℂ) + Complex.exp ((n : ℂ) + (y : ℂ) * I)) *
      ((n : ℂ) + (y : ℂ) * I - (Real.pi : ℂ) * I))) atTop (𝓝 0) := by
  have he : ∀ᶠ n : ℕ in atTop, 3 * x / 2 ≤ Real.exp (n : ℝ) :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (3 * x / 2))
  have hb : Tendsto (fun n : ℕ => (2 / (x * (n : ℝ))) * (2 * Real.pi))
      atTop (𝓝 0) := by
    simpa [div_mul_eq_div_div] using
      ((tendsto_const_div_atTop_nhds_zero_nat (2 / x)).mul_const (2 * Real.pi))
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hne hn
  simpa only [Nat.cast_nonneg, abs_of_nonneg, Complex.ofReal_natCast] using
    vertical_integral_bound x (n : ℝ) hx (by exact_mod_cast hn.ne') (Or.inr hne)

theorem vertical_left_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => ∫ y in (0 : ℝ)..2 * Real.pi,
      1 / (((x : ℂ) + Complex.exp (-(n : ℂ) + (y : ℂ) * I)) *
      (-(n : ℂ) + (y : ℂ) * I - (Real.pi : ℂ) * I))) atTop (𝓝 0) := by
  have he : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) ≤ x / 2 :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_le_nhds (by positivity : (0 : ℝ) < x / 2))
  have hb : Tendsto (fun n : ℕ => (2 / (x * (n : ℝ))) * (2 * Real.pi))
      atTop (𝓝 0) := by
    simpa [div_mul_eq_div_div] using
      ((tendsto_const_div_atTop_nhds_zero_nat (2 / x)).mul_const (2 * Real.pi))
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hne hn
  simpa only [abs_neg, Nat.cast_nonneg, abs_of_nonneg, ofReal_neg, Complex.ofReal_natCast] using
    vertical_integral_bound x (-(n : ℝ)) hx
      (neg_ne_zero.mpr (by exact_mod_cast hn.ne'))
      (Or.inl hne)

private lemma stripWeight_integral_reduction (x : ℝ) (hx : 0 < x) :
    (∫ s : ℝ, stripWeight x s) =
      1 - x * (∫ s : ℝ, 1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2))) := by
  have hfn : stripWeight x = fun s : ℝ =>
      1 / (s ^ 2 + Real.pi ^ 2) -
        x * (1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2))) := by
    funext s
    unfold stripWeight
    have hd : s ^ 2 + Real.pi ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have he : x + Real.exp s ≠ 0 := ne_of_gt (by positivity)
    field_simp [hd, he]
    <;> ring
  rw [hfn, integral_sub lorentz_integrable ((reciprocalStrip_integrable x hx).const_mul x),
    lorentz_integral, integral_const_mul]

private lemma horizontal_den_ne_zero (s : ℝ) (sign : ℝ) (hsign : sign ≠ 0) :
    (s : ℂ) + (sign : ℂ) * I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add, zero_im] at hi
  exact hsign hi

private lemma horizontal_pair_algebra (x s : ℝ) (hx : 0 < x) :
    1 / (((x : ℂ) + (Real.exp s : ℂ)) * ((s : ℂ) - (Real.pi : ℂ) * I)) -
      1 / (((x : ℂ) + (Real.exp s : ℂ)) * ((s : ℂ) + (Real.pi : ℂ) * I)) =
      (2 * (Real.pi : ℂ) * I) *
        ((1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2)) : ℝ) : ℂ) := by
  have hbottom : (s : ℂ) - (Real.pi : ℂ) * I ≠ 0 := by
    simpa only [sub_eq_add_neg, ← neg_mul, ← ofReal_neg] using
      horizontal_den_ne_zero s (-Real.pi) (neg_ne_zero.mpr Real.pi_ne_zero)
  have htop := horizontal_den_ne_zero s Real.pi Real.pi_ne_zero
  have he : (x : ℂ) + (Real.exp s : ℂ) ≠ 0 := by
    norm_cast
    positivity
  have hd : (s ^ 2 + Real.pi ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hdc : (s : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_pow]
  field_simp [hbottom, htop, he, hdc]
  ring_nf
  simp [Complex.I_sq]

private lemma horizontal_pair_integral (x a b : ℝ) (hx : 0 < x) :
    (∫ s in a..b, 1 / (((x : ℂ) + (Real.exp s : ℂ)) *
      ((s : ℂ) - (Real.pi : ℂ) * I))) -
      (∫ s in a..b, 1 / (((x : ℂ) + (Real.exp s : ℂ)) *
      ((s : ℂ) + (Real.pi : ℂ) * I))) =
      (2 * (Real.pi : ℂ) * I) *
        ((∫ s in a..b, 1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2)) : ℝ) : ℂ) := by
  have he : ∀ s : ℝ, (x : ℂ) + (Real.exp s : ℂ) ≠ 0 := by
    intro s
    norm_cast
    positivity
  have cb : Continuous (fun s : ℝ => 1 /
      (((x : ℂ) + (Real.exp s : ℂ)) * ((s : ℂ) - (Real.pi : ℂ) * I))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro s
    apply mul_ne_zero (he s)
    simpa only [sub_eq_add_neg, ← neg_mul, ← ofReal_neg] using
      horizontal_den_ne_zero s (-Real.pi) (neg_ne_zero.mpr Real.pi_ne_zero)
  have ct : Continuous (fun s : ℝ => 1 /
      (((x : ℂ) + (Real.exp s : ℂ)) * ((s : ℂ) + (Real.pi : ℂ) * I))) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro s
    exact mul_ne_zero (he s) (horizontal_den_ne_zero s Real.pi Real.pi_ne_zero)
  rw [← intervalIntegral.integral_sub (cb.intervalIntegrable a b) (ct.intervalIntegrable a b)]
  simp_rw [horizontal_pair_algebra x _ hx]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]

private lemma rectangle_horizontal_pair (x T : ℝ) (hx : 0 < x) :
    RectangleIntegral (stripPoleKernel x) (-T : ℂ) ((T : ℂ) + (2 * Real.pi : ℂ) * I) =
      (2 * (Real.pi : ℂ) * I) *
        ((∫ s in -T..T, 1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2)) : ℝ) : ℂ) +
        I * (∫ y in (0 : ℝ)..2 * Real.pi, stripPoleKernel x ((T : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in (0 : ℝ)..2 * Real.pi, stripPoleKernel x (-(T : ℂ) + (y : ℂ) * I)) := by
  have hb : ∀ s : ℝ, stripPoleKernel x (s : ℂ) =
      1 / (((x : ℂ) + (Real.exp s : ℂ)) * ((s : ℂ) - (Real.pi : ℂ) * I)) := by
    intro s
    simp only [stripPoleKernel, Complex.ofReal_exp]
  have ht : ∀ s : ℝ, stripPoleKernel x ((s : ℂ) + (2 * Real.pi : ℂ) * I) =
      1 / (((x : ℂ) + (Real.exp s : ℂ)) * ((s : ℂ) + (Real.pi : ℂ) * I)) := by
    intro s
    rw [stripPoleKernel, exp_upper_boundary]
    congr 2
    ring
  simp only [RectangleIntegral, HIntegral, VIntegral, ofReal_neg, neg_re, neg_im,
    ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im,
    Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, sub_zero, neg_zero]
  simp only [Complex.ofReal_zero, Complex.ofReal_mul, Complex.ofReal_ofNat,
    zero_mul, add_zero, hb, ht, smul_eq_mul]
  rw [horizontal_pair_integral x (-T) T hx]

theorem reciprocalStrip_integral (x : ℝ) (hx : 0 < x) (hne : x ≠ 1) :
    (∫ s : ℝ, 1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2))) =
      1 / (x - 1) - 1 / (x * Real.log x) := by
  have hi := intervalIntegral_tendsto_integral (reciprocalStrip_integrable x hx)
    (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)) tendsto_natCast_atTop_atTop
  have hc := ((Complex.continuous_ofReal.tendsto _).comp hi).const_mul
    (2 * (Real.pi : ℂ) * I)
  have hr := (vertical_right_tendsto x hx).const_mul I
  have hl := (vertical_left_tendsto x hx).const_mul I
  have hlim : Tendsto (fun n : ℕ =>
      RectangleIntegral (stripPoleKernel x) (-(n : ℝ) : ℂ)
        ((n : ℂ) + (2 * Real.pi : ℂ) * I)) atTop
      (𝓝 ((2 * (Real.pi : ℂ) * I) *
        ((∫ s : ℝ, 1 / ((x + Real.exp s) * (s ^ 2 + Real.pi ^ 2)) : ℝ) : ℂ))) := by
    have hh := (hc.add hr).sub hl
    simp only [mul_zero, add_zero, sub_zero] at hh
    convert hh using 1
    funext n
    simp only [← Complex.ofReal_natCast]
    rw [rectangle_horizontal_pair x (n : ℝ) hx]
    simp only [stripPoleKernel, ofReal_neg, Complex.ofReal_natCast, Function.comp_apply]
  have he : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ∧ |Real.log x| < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (max (0 : ℝ) |Real.log x|)) |>.mono
      (fun n hn => ⟨lt_of_le_of_lt (le_max_left _ _) hn,
        lt_of_le_of_lt (le_max_right _ _) hn⟩)
  have hconst : Tendsto (fun n : ℕ =>
      RectangleIntegral (stripPoleKernel x) (-(n : ℝ) : ℂ)
        ((n : ℂ) + (2 * Real.pi : ℂ) * I)) atTop
      (𝓝 ((2 * (Real.pi : ℂ) * I) *
        (1 / ((x : ℂ) - 1) - 1 / ((x : ℂ) * (Real.log x : ℂ))))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simpa only [Complex.ofReal_natCast] using
      (stripPoleKernel_rectangle hx hne hn.1 hn.2).symm
  have heq := tendsto_nhds_unique hlim hconst
  have hpi : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hv := mul_left_cancel₀ hpi heq
  exact_mod_cast hv

theorem stripWeight_integral (x : ℝ) (hx : 0 < x) (hne : x ≠ 1) :
    (∫ s : ℝ, stripWeight x s) = 1 / Real.log x - 1 / (x - 1) := by
  rw [stripWeight_integral_reduction x hx, reciprocalStrip_integral x hx hne]
  have hl := Real.log_ne_zero_of_pos_of_ne_one hx hne
  have hm : x - 1 ≠ 0 := sub_ne_zero.mpr hne
  field_simp [hx.ne', hl, hm]
  <;> ring

end D5.S3.Quantum.PositiveResolvent.MasterStripLimits
