/- GID: D5/S3/Analysis/ScreenAnisotropy
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-shear-obstruction4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The determinant-normalized angular factor of a positive diagonal screen form is a Poisson kernel at twice the angle. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
Omega original.

The determinant-normalized angular factor of a positive diagonal screen form is a
Poisson kernel at twice the angle. Its first and second moments follow from the
Poisson integral formula on the unit disk.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace Omega.ScreenAnisotropy

/-- The determinant-normalized angular factor of a diagonal screen form. -/
def factor (x y θ : ℝ) : ℝ :=
  Real.sqrt (x * y) / (x * Real.cos θ ^ 2 + y * Real.sin θ ^ 2)

/-- The radial parameter of the corresponding disk Poisson kernel. -/
def parameter (x y : ℝ) : ℝ :=
  (Real.sqrt y - Real.sqrt x) / (Real.sqrt y + Real.sqrt x)

/-- The unit disk Poisson kernel in angular coordinates. -/
def poisson (t θ : ℝ) : ℝ :=
  (1 - t ^ 2) / (1 - 2 * t * Real.cos θ + t ^ 2)

private theorem screen_denom_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (θ : ℝ) :
    0 < x * Real.cos θ ^ 2 + y * Real.sin θ ^ 2 := by
  calc
    0 < min x y * 1 := by simpa only [mul_one] using lt_min hx hy
    _ = min x y * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by rw [Real.cos_sq_add_sin_sq]
    _ ≤ x * Real.cos θ ^ 2 + y * Real.sin θ ^ 2 := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left x y) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (min_le_right x y) (sq_nonneg _))

theorem continuous_factor {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Continuous (factor x y) := by
  unfold factor
  exact continuous_const.div (by fun_prop) (fun θ ↦ (screen_denom_pos hx hy θ).ne')

theorem factor_self {x : ℝ} (hx : 0 < x) (θ : ℝ) : factor x x θ = 1 := by
  rw [factor, Real.sqrt_mul_self hx.le, ← mul_add, Real.cos_sq_add_sin_sq, mul_one,
    div_self hx.ne']

private theorem abs_parameter_lt_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |parameter x y| < 1 := by
  have hx' := Real.sqrt_pos.2 hx
  have hy' := Real.sqrt_pos.2 hy
  have hsum : 0 < Real.sqrt y + Real.sqrt x := by positivity
  rw [parameter, abs_div, abs_of_pos hsum, div_lt_one hsum, abs_lt]
  constructor <;> linarith

theorem parameter_mem_Ioo {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    parameter x y ∈ Ioo (0 : ℝ) 1 := by
  have hy := hx.trans hxy
  refine ⟨?_, (le_abs_self _).trans_lt (abs_parameter_lt_one hx hy)⟩
  unfold parameter
  exact div_pos (sub_pos.2 (Real.sqrt_lt_sqrt hx.le hxy)) (by positivity)

theorem factor_eq_poisson {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (θ : ℝ) :
    factor x y θ = poisson (parameter x y) (2 * θ) := by
  let a := Real.sqrt x
  let b := Real.sqrt y
  have ha : a ^ 2 = x := Real.sq_sqrt hx.le
  have hb : b ^ 2 = y := Real.sq_sqrt hy.le
  have hs : b + a ≠ 0 := (add_pos (Real.sqrt_pos.2 hy) (Real.sqrt_pos.2 hx)).ne'
  have hn : 1 - ((b - a) / (b + a)) ^ 2 = 4 * a * b / (b + a) ^ 2 := by
    field_simp [hs]
    ring
  have hd : 1 - 2 * ((b - a) / (b + a)) * Real.cos (2 * θ)
        + ((b - a) / (b + a)) ^ 2 =
      4 * (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) / (b + a) ^ 2 := by
    rw [Real.cos_two_mul']
    field_simp [hs]
    linear_combination -(2 * a ^ 2 + 2 * b ^ 2) * Real.cos_sq_add_sin_sq θ
  unfold factor poisson parameter
  rw [Real.sqrt_mul hx.le]
  change a * b / (x * Real.cos θ ^ 2 + y * Real.sin θ ^ 2) = _
  rw [hn, hd, ha, hb]
  field_simp [hs, (screen_denom_pos hx hy θ).ne']

private def cayleyRe (s : ℝ) (z : ℂ) : ℝ :=
  ((1 + (s : ℂ) * z) / (1 - (s : ℂ) * z)).re

private theorem cayleyRe_harmonic {s : ℝ} (hs : |s| < 1) :
    InnerProductSpace.HarmonicOnNhd (cayleyRe s) (closedBall (0 : ℂ) 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
  have hne : 1 - (s : ℂ) * z ≠ 0 := by
    intro h
    have heq : (s : ℂ) * z = 1 := (sub_eq_zero.1 h).symm
    have hn : |s| * ‖z‖ = 1 := by
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using congrArg norm heq
    exact (not_lt_of_ge hn.ge) ((mul_le_mul_of_nonneg_left hz' (abs_nonneg _)).trans_lt
      (by simpa using hs))
  have ha : AnalyticAt ℂ (fun w : ℂ ↦ (1 + (s : ℂ) * w) / (1 - (s : ℂ) * w)) z := by
    exact ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))) hne
  exact ha.harmonicAt_re

private theorem unit_circle_re_im (θ : ℝ) :
    (circleMap 0 1 θ).re = Real.cos θ ∧ (circleMap 0 1 θ).im = Real.sin θ := by
  simp [circleMap_zero, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

private theorem poissonKernel_circle (r θ : ℝ) :
    poissonKernel 0 (r : ℂ) (circleMap 0 1 θ) = poisson r θ := by
  obtain ⟨hre, him⟩ := unit_circle_re_im θ
  rw [poissonKernel_def, sub_zero, sub_zero, norm_circleMap_zero, abs_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, one_pow, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    sub_zero, hre, him]
  unfold poisson
  congr 1
  linear_combination Real.cos_sq_add_sin_sq θ

private theorem cayleyRe_circle (s θ : ℝ) :
    cayleyRe s (circleMap 0 1 θ) = poisson s θ := by
  obtain ⟨hre, him⟩ := unit_circle_re_im θ
  have hden : Complex.normSq (1 - (s : ℂ) * circleMap 0 1 θ) =
      1 - 2 * s * Real.cos θ + s ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero, hre, him]
    linear_combination s ^ 2 * Real.cos_sq_add_sin_sq θ
  rw [cayleyRe, Complex.div_re, ← add_div, hden, poisson]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, zero_add, hre, him]
  congr 1
  linear_combination -s ^ 2 * Real.cos_sq_add_sin_sq θ

private theorem poisson_inner {r s : ℝ} (hr : |r| < 1) (hs : |s| < 1) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, poisson r θ * poisson s θ) =
      2 * Real.pi * (1 + r * s) / (1 - r * s) := by
  have hw : (r : ℂ) ∈ ball 0 1 := by
    simpa [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using hr
  have heq := (cayleyRe_harmonic hs).circleAverage_poissonKernel_smul hw
  rw [Real.circleAverage_def] at heq
  simp only [smul_eq_mul, Pi.mul_apply, poissonKernel_circle, cayleyRe_circle] at heq
  have hvalue : cayleyRe s (r : ℂ) = (1 + r * s) / (1 - r * s) := by
    unfold cayleyRe
    rw [← Complex.ofReal_one, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re,
      mul_comm s r]
  rw [hvalue] at heq
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  calc
    (∫ θ in (0 : ℝ)..2 * Real.pi, poisson r θ * poisson s θ) =
        (2 * Real.pi) *
          ((2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, poisson r θ * poisson s θ)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
    _ = 2 * Real.pi * (1 + r * s) / (1 - r * s) := by rw [heq, mul_div_assoc]

private theorem integral_double_angle (f : ℝ → ℝ) (hcont : Continuous f)
    (hperiodic : Function.Periodic f (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f (2 * θ)) = ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
  rw [intervalIntegral.integral_comp_mul_left f (by norm_num : (2 : ℝ) ≠ 0), mul_zero,
    smul_eq_mul]
  have hadd : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) +
      (∫ θ in 2 * Real.pi..2 * (2 * Real.pi), f θ) =
        ∫ θ in (0 : ℝ)..2 * (2 * Real.pi), f θ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hshift : (∫ θ in 2 * Real.pi..2 * (2 * Real.pi), f θ) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
    simpa only [zero_add, ← two_mul] using (hperiodic.intervalIntegral_add_eq 0 (2 * Real.pi)).symm
  rw [← hadd, hshift]
  ring

private theorem poisson_continuous {r : ℝ} (hr : |r| < 1) : Continuous (poisson r) := by
  have hden (θ : ℝ) : 0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
    have hle : r * Real.cos θ ≤ |r| :=
      (le_abs_self _).trans (by rw [abs_mul]; simpa using
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg r))
    have hsq : 0 < (1 - |r|) ^ 2 := by positivity
    nlinarith [sq_abs r]
  unfold poisson
  exact continuous_const.div (by fun_prop) (fun θ ↦ (hden θ).ne')

private theorem poisson_periodic (r : ℝ) : Function.Periodic (poisson r) (2 * Real.pi) :=
  fun θ ↦ by simp [poisson, Real.cos_add_two_pi]

theorem factor_inner {x y x' y' : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hx' : 0 < x') (hy' : 0 < y') :
    (∫ θ in (0 : ℝ)..2 * Real.pi, factor x y θ * factor x' y' θ) =
      2 * Real.pi * (1 + parameter x y * parameter x' y') /
        (1 - parameter x y * parameter x' y') := by
  have hr := abs_parameter_lt_one hx hy
  have hs := abs_parameter_lt_one hx' hy'
  simp_rw [factor_eq_poisson hx hy, factor_eq_poisson hx' hy']
  rw [integral_double_angle (fun θ ↦ poisson (parameter x y) θ * poisson (parameter x' y') θ)
    ((poisson_continuous hr).mul (poisson_continuous hs))
    ((poisson_periodic _).mul (poisson_periodic _))]
  exact poisson_inner hr hs

theorem factor_average {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (1 / (2 * Real.pi)) * (∫ θ in (0 : ℝ)..2 * Real.pi, factor x y θ) = 1 := by
  have hp : parameter 1 1 = 0 := by simp [parameter]
  have hint : (∫ θ in (0 : ℝ)..2 * Real.pi, factor x y θ) = 2 * Real.pi := by
    simpa only [factor_self zero_lt_one, hp, mul_one, mul_zero, add_zero, sub_zero, div_one] using
      factor_inner hx hy zero_lt_one zero_lt_one
  rw [hint]
  field_simp [Real.pi_ne_zero]

theorem integral_sq_pos_of_ne_zero {C : ℝ → ℝ} (hC : Continuous C) (h0 : C 0 ≠ 0) :
    0 < ∫ θ in (0 : ℝ)..2 * Real.pi, (C θ) ^ 2 := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ ↦ (0 : ℝ)) (g := fun θ ↦ (C θ) ^ 2) hπ
    continuous_const.continuousOn (hC.pow 2).continuousOn (fun θ _ ↦ sq_nonneg (C θ))
    ⟨0, ⟨le_rfl, hπ.le⟩, sq_pos_of_ne_zero h0⟩
  simpa using h

end Omega.ScreenAnisotropy
