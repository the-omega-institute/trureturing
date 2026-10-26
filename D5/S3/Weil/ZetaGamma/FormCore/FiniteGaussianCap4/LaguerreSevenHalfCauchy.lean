/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfCauchy
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Gaussian generating-function helper for the original finite-source comparison. -/

/-
SPDX-License-Identifier: Apache-2.0
UNCOMPILED independent source proposal, 2026-10-26.
No compiler, kernel, or official acceptance is asserted.

The coefficient estimate uses the actual generating function and Cauchy's
estimate. The absolute double-series majorant is not used for decay in x.

The elementary `mobius_re` calculation specializes the proof method in
Mathlib.Analysis.Complex.Poisson, private declaration
poissonKernel_eq_re_herglotzRieszKernel_aux, to a=1. That source is
Copyright (c) 2026 Stefan Kebekus. Authors: Mihai Iancu, Stefan Kebekus,
Sebastian Schleissinger. Released under Apache-2.0; see ../LICENSE-Mathlib.
This modified file supplies the circle inequality and the Laguerre estimate.
-/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfGenerating
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped BigOperators Topology

namespace FiniteGaussianCap4.LaguerreSevenHalf

/-- The branch condition is verified on the whole open unit disk. -/
theorem one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) :
    1 - z ∈ Complex.slitPlane := by
  simpa only [sub_eq_add_neg] using
    Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)

theorem generating_differentiableAt (x : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (generating x) z := by
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z :=
    (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
  have hne : (1 : ℂ) - z ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_mem_slitPlane hz)
  have he : DifferentiableAt ℂ
      (fun w : ℂ => -(x : ℂ) * (1 + w) / (1 - w)) z :=
    ((differentiableAt_const (-(x : ℂ))).mul
      ((differentiableAt_const (1 : ℂ)).add differentiableAt_id)).div hd hne
  exact (hd.cpow_const (one_sub_mem_slitPlane hz)).mul he.cexp

/-- Cauchy's hypotheses hold on every smaller closed disk. -/
theorem generating_diffContOnCl (x : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    DiffContOnCl ℂ (generating x) (ball 0 r) := by
  apply DifferentiableOn.diffContOnCl_ball (U := ball (0 : ℂ) 1)
  · intro z hz
    exact (generating_differentiableAt x (by simpa using hz)).differentiableWithinAt
  · intro z hz
    have hz' : ‖z‖ ≤ r := by simpa using hz
    simpa using hz'.trans_lt hr1

/-- Exact real part, before any estimate of the denominator. -/
theorem mobius_re (z : ℂ) :
    ((1 + z) / (1 - z)).re = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
  rw [Complex.div_re, Complex.normSq_eq_norm_sq, ← add_div]
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_add, zero_sub]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Sharp disk-to-half-plane estimate on the circle of radius r. -/
theorem mobius_re_lower {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = r) :
    (1 - r) / (1 + r) ≤ ((1 + z) / (1 - z)).re := by
  have hlo : 1 - r ≤ ‖1 - z‖ := by
    simpa only [norm_one, hz] using norm_sub_norm_le (1 : ℂ) z
  have hup : ‖1 - z‖ ≤ 1 + r := by
    simpa only [norm_one, hz] using norm_sub_le (1 : ℂ) z
  have hd : 0 < ‖1 - z‖ := lt_of_lt_of_le (sub_pos.mpr hr1) hlo
  have hd2 : 0 < ‖1 - z‖ ^ 2 := sq_pos_of_pos hd
  have hp : 0 < 1 + r := by linarith
  have hsq : ‖1 - z‖ ^ 2 ≤ (1 + r) ^ 2 := by
    nlinarith [norm_nonneg (1 - z)]
  rw [mobius_re, hz]
  apply (div_le_div_iff₀ hp hd2).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) (sub_nonneg.mpr hsq)]

/-- A positive decay rate for every r in (0,1). -/
def circleDecay (r : ℝ) : ℝ := (1 - r) / (1 + r)

theorem circleDecay_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < circleDecay r := by
  exact div_pos (sub_pos.mpr hr1) (by linarith)

/-- Uniform Gaussian decay on the complex circle. -/
theorem generating_norm_on_circle (x : ℝ) (hx : 0 ≤ x) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ = r) :
    ‖generating x z‖ ≤
      (1 - r) ^ (-9 / 2 : ℝ) * Real.exp (-circleDecay r * x) := by
  have hlo : 1 - r ≤ ‖1 - z‖ := by
    simpa only [norm_one, hz] using norm_sub_norm_le (1 : ℂ) z
  have hp : ‖1 - z‖ ^ (-9 / 2 : ℝ) ≤ (1 - r) ^ (-9 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hr1) hlo (by norm_num)
  have hm : circleDecay r ≤ ((1 + z) / (1 - z)).re :=
    mobius_re_lower hr hr1 hz
  have he : (-(x : ℂ) * (1 + z) / (1 - z)).re =
      -x * ((1 + z) / (1 - z)).re := by
    rw [mul_div_assoc]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  have hexp : Real.exp (-x * ((1 + z) / (1 - z)).re) ≤
      Real.exp (-circleDecay r * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hm)]
  rw [generating, norm_mul, Complex.norm_cpow_real, Complex.norm_exp, he]
  exact mul_le_mul hp hexp (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)

/-- Cauchy's estimate applied after the explicit coefficient identification.
The inverse natural power is r^(-n). -/
theorem phi_coefficient_bound (x : ℝ) (hx : 0 ≤ x) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    |phi x n| ≤ (1 - r) ^ (-9 / 2 : ℝ) * (r ^ n)⁻¹ *
      Real.exp (-circleDecay r * x) := by
  let C : ℝ := (1 - r) ^ (-9 / 2 : ℝ) * Real.exp (-circleDecay r * x)
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (f := generating x) (c := 0) (R := r) (C := C) n hr
    (generating_diffContOnCl x hr hr1) (fun z hz => by
      apply generating_norm_on_circle x hx hr hr1
      simpa only [Metric.mem_sphere, dist_zero_right] using hz)
  rw [generating_iteratedDeriv, norm_mul, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs] at hc
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  have hquot : |phi x n| ≤ C / r ^ n := by
    apply (mul_le_mul_iff_right₀ hfact).mp
    simpa only [mul_div_assoc] using hc
  calc
    |phi x n| ≤ C / r ^ n := hquot
    _ = (1 - r) ^ (-9 / 2 : ℝ) * (r ^ n)⁻¹ *
        Real.exp (-circleDecay r * x) := by
      dsimp [C]
      ring

/-- The literal real-exponent version of the requested bound. -/
theorem phi_coefficient_bound_rpow (x : ℝ) (hx : 0 ≤ x) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (n : ℕ) :
    |phi x n| ≤ (1 - r) ^ (-9 / 2 : ℝ) * r ^ (-(n : ℝ)) *
      Real.exp (-((1 - r) / (1 + r)) * x) := by
  simpa only [circleDecay, Real.rpow_neg hr.le, Real.rpow_natCast] using
    phi_coefficient_bound x hx hr hr1 n

/-- Geometric domination retains Gaussian decay for arbitrary |q|<r<1. -/
theorem phi_geometric_bound (x : ℝ) (hx : 0 ≤ x) (q : ℝ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hqr : |q| < r) (n : ℕ) :
    |phi x n * q ^ n| ≤
      ((1 - r) ^ (-9 / 2 : ℝ) * Real.exp (-circleDecay r * x)) *
        (|q| / r) ^ n := by
  rw [abs_mul, abs_pow]
  calc
    |phi x n| * |q| ^ n ≤
        ((1 - r) ^ (-9 / 2 : ℝ) * (r ^ n)⁻¹ *
          Real.exp (-circleDecay r * x)) * |q| ^ n :=
      mul_le_mul_of_nonneg_right (phi_coefficient_bound x hx hr hr1 n)
        (pow_nonneg (abs_nonneg q) n)
    _ = ((1 - r) ^ (-9 / 2 : ℝ) * Real.exp (-circleDecay r * x)) *
        (|q| / r) ^ n := by
      rw [div_pow]
      ring

/-- The same complex domination is available for norm-convergent series. -/
theorem phi_geometric_bound_complex (x : ℝ) (hx : 0 ≤ x) (z : ℂ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hzr : ‖z‖ < r) (n : ℕ) :
    ‖(phi x n : ℂ) * z ^ n‖ ≤
      ((1 - r) ^ (-9 / 2 : ℝ) * Real.exp (-circleDecay r * x)) *
        (‖z‖ / r) ^ n := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  calc
    |phi x n| * ‖z‖ ^ n ≤
        ((1 - r) ^ (-9 / 2 : ℝ) * (r ^ n)⁻¹ *
          Real.exp (-circleDecay r * x)) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right (phi_coefficient_bound x hx hr hr1 n)
        (pow_nonneg (norm_nonneg z) n)
    _ = ((1 - r) ^ (-9 / 2 : ℝ) * Real.exp (-circleDecay r * x)) *
        (‖z‖ / r) ^ n := by
      rw [div_pow]
      ring

/-- Weighted exponential majorants are integrable for all three physical powers
5/4 (L1), 7/2 (H after squaring), and 11/2 (the x graph after squaring).
This is an actual scalar integrability theorem, not an asserted L2 limit. -/
theorem integrable_decay_weight (s b : ℝ) (hs : -1 < s) (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun x : ℝ => x ^ s * Real.exp (-b * x)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) hs (by norm_num) hb)

theorem integrable_cauchy_L1_majorant {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (5 / 4 : ℝ) * Real.exp (-circleDecay r * x)) (Ioi 0) := by
  exact integrable_decay_weight _ _ (by norm_num) (circleDecay_pos hr hr1)

theorem integrable_cauchy_H_majorant {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (7 / 2 : ℝ) * Real.exp (-(2 * circleDecay r) * x))
      (Ioi 0) := by
  exact integrable_decay_weight _ _ (by norm_num)
    (mul_pos (by norm_num) (circleDecay_pos hr hr1))

theorem integrable_cauchy_graph_majorant {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (11 / 2 : ℝ) * Real.exp (-(2 * circleDecay r) * x))
      (Ioi 0) := by
  exact integrable_decay_weight _ _ (by norm_num)
    (mul_pos (by norm_num) (circleDecay_pos hr hr1))

end FiniteGaussianCap4.LaguerreSevenHalf
