import OmegaBuild.Commands
import OmegaMath.Analysis.LogisticCoordinate
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

The elementary half-integer Bessel correction in modular coordinates.
The separate roots of the two logistic coordinates give a single-valued
holomorphic continuation and a quantitative double Fourier estimate.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ComplexConjugate

namespace Omega

/-- The denominator in the complex logistic coordinate at rate (2\pi). -/
private def modularDenom (z : ℂ) : ℂ := 1 + Complex.exp (2 * Real.pi * z)

/-- The principal square root of the logistic coordinate, continued as a quotient
with a separate square root in its denominator. -/
def modularRoot (z : ℂ) : ℂ :=
  Complex.exp (Real.pi * z) / modularDenom z ^ (2⁻¹ : ℂ)

/-- The complex continuation of the logistic Jacobian. -/
def modularJacobian (z : ℂ) : ℂ :=
  2 * Real.pi * Complex.exp (2 * Real.pi * z) / modularDenom z ^ 2

theorem modularDenom_mem_slitPlane (z : ℂ) (hz : |z.im| < 1 / 2) :
    (1 + Complex.exp (2 * Real.pi * z)) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have htheta : |2 * Real.pi * z.im| < Real.pi := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    nlinarith [mul_lt_mul_of_pos_left hz Real.pi_pos]
  have he : ((2 : ℂ) * Real.pi * z).im = 2 * Real.pi * z.im := by simp [Complex.mul_im]
  have hr : ((2 : ℂ) * Real.pi * z).re = 2 * Real.pi * z.re := by simp [Complex.mul_re]
  by_cases hi : (1 + Complex.exp (2 * Real.pi * z)).im = 0
  · left
    simp only [Complex.add_im, Complex.one_im, zero_add, Complex.exp_im, he, hr] at hi
    have hs := (mul_eq_zero.mp hi).resolve_left (Real.exp_ne_zero _)
    have ht := (Real.sin_eq_zero_iff_of_lt_of_lt (abs_lt.mp htheta).1
      (abs_lt.mp htheta).2).mp hs
    rw [Complex.add_re, Complex.one_re, Complex.exp_re, he, hr, ht, Real.cos_zero, mul_one]
    positivity
  · exact Or.inr hi

theorem modularRoot_differentiableOn :
    DifferentiableOn ℂ modularRoot {z : ℂ | |z.im| < 1 / 2} := by
  intro z hz
  have hd : DifferentiableAt ℂ modularDenom z := by unfold modularDenom; fun_prop
  have hs : modularDenom z ∈ Complex.slitPlane := modularDenom_mem_slitPlane z hz
  exact ((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (Real.pi * z)) z).div
    (hd.cpow_const hs)
    (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num : (2⁻¹ : ℂ) ≠ 0)
      |>.mpr (Complex.slitPlane_ne_zero hs))).differentiableWithinAt

theorem modularRoot_continuousOn :
    ContinuousOn modularRoot {z : ℂ | |z.im| ≤ 3 / 8} :=
  modularRoot_differentiableOn.continuousOn.mono fun z hz => by
    change |z.im| < (1 : ℝ) / 2
    exact lt_of_le_of_lt (show |z.im| ≤ (3 : ℝ) / 8 from hz) (by norm_num)

private theorem modularJacobian_differentiableOn :
    DifferentiableOn ℂ modularJacobian {z : ℂ | |z.im| < 1 / 2} := by
  intro z hz
  have hn : modularDenom z ≠ 0 := Complex.slitPlane_ne_zero (modularDenom_mem_slitPlane z hz)
  have hd : DifferentiableAt ℂ modularDenom z := by unfold modularDenom; fun_prop
  exact ((by fun_prop : DifferentiableAt ℂ
    (fun z : ℂ => 2 * Real.pi * Complex.exp (2 * Real.pi * z)) z).div
    (hd.pow 2) (pow_ne_zero _ hn)).differentiableWithinAt

private theorem modularRoot_measurable : Measurable modularRoot := by
  have hD : Measurable modularDenom := by unfold modularDenom; fun_prop
  have hp : Measurable (fun z : ℂ => z ^ (2⁻¹ : ℂ)) := by
    simp only [Complex.cpow_def, show (2⁻¹ : ℂ) ≠ 0 by norm_num, ite_false]
    exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (Complex.continuous_exp.measurable.comp (Complex.measurable_log.mul measurable_const))
  exact (by fun_prop : Measurable (fun z : ℂ => Complex.exp (Real.pi * z))).div (hp.comp hD)

private theorem modularJacobian_measurable : Measurable modularJacobian := by
  unfold modularJacobian modularDenom
  fun_prop

private theorem modularDenom_ofReal (r : ℝ) :
    modularDenom (r : ℂ) = ((1 + Real.exp (2 * Real.pi * r) : ℝ) : ℂ) := by
  simp [modularDenom, Complex.ofReal_exp]

/-- The branch chosen for the continuation is the nonnegative logistic root on the real line. -/
theorem modularRoot_ofReal (r : ℝ) :
    modularRoot (r : ℂ) = (Real.sqrt (logistic (2 * Real.pi) r) : ℂ) := by
  have hd : 0 ≤ 1 + Real.exp (2 * Real.pi * r) := by positivity
  have hcast : (2⁻¹ : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; norm_num
  rw [modularRoot, modularDenom_ofReal, hcast, ← Complex.ofReal_cpow hd,
    ← Real.sqrt_eq_rpow, logistic_eq_exp, Real.sqrt_div (Real.exp_pos _).le, ← Real.exp_half]
  push_cast
  congr 2
  ring

theorem modularJacobian_ofReal (r : ℝ) :
    modularJacobian (r : ℂ) =
      ((2 * Real.pi * Real.exp (2 * Real.pi * r) /
      (1 + Real.exp (2 * Real.pi * r)) ^ 2 : ℝ) : ℂ) := by
  simp [modularJacobian, modularDenom_ofReal, Complex.ofReal_exp]

/-- The elementary mixed radial correction on the continued modular coordinates. -/
def correction5D_holo (M : ℝ) (z w : ℂ) (x : ℝ) : ℂ :=
  let L : ℂ := (M * Real.sqrt (2 * (1 - x)) : ℝ)
  let Z := L * modularRoot z * modularRoot w
  ((M ^ 2 / (32 * Real.pi ^ 2 * Real.sqrt (2 * (1 - x))) : ℝ) : ℂ) *
    Complex.exp (-Z) * (Z - 2)

/-- The correction multiplied by the modular Jacobians, with zero on angular coincidence. -/
def kernelG5D (M : ℝ) (z w : ℂ) (x : ℝ) : ℂ :=
  if x < 1 then 4 * modularJacobian z * modularJacobian w * correction5D_holo M z w x else 0

private theorem kernelG5D_swap (M : ℝ) (z w : ℂ) (x : ℝ) :
    kernelG5D M z w x = kernelG5D M w z x := by
  by_cases hx : x < 1
  · simp only [kernelG5D, correction5D_holo, ite_eq_left hx]
    rw [show ((↑(M * √(2 * (1 - x))) : ℂ) * modularRoot z * modularRoot w) =
      (↑(M * √(2 * (1 - x))) : ℂ) * modularRoot w * modularRoot z by ring]
    ring
  · simp [kernelG5D, hx]

private theorem kernelG5D_conj_real (M r s x : ℝ) :
    conj (kernelG5D M r s x) = kernelG5D M r s x := by
  by_cases hx : x < 1
  · simp [kernelG5D, hx, correction5D_holo, modularRoot_ofReal, modularJacobian_ofReal,
      ← Complex.exp_conj, map_ofNat]
  · simp [kernelG5D, hx]

private def fourierIntegrand (M ν lam x : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (ν : ℂ) * z + Complex.I * (lam : ℂ) * w) * kernelG5D M z w x

/-- The mixed-sign two-dimensional Fourier transform, at unitary normalization. -/
def fourierG5D (M ν lam x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, ∫ s : ℝ, fourierIntegrand M ν lam x r s

theorem fourierG5D_zero (M ν lam : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    fourierG5D M ν lam x = 0 := by
  simp [fourierG5D, fourierIntegrand, kernelG5D, not_lt_of_ge hx]

private theorem measurable_fourierIntegrand {α : Type*} [MeasurableSpace α] (M : ℝ)
    {ν lam x : α → ℝ} {z w : α → ℂ} (hν : Measurable ν) (hlam : Measurable lam)
    (hx : Measurable x) (hz : Measurable z) (hw : Measurable w) :
    Measurable (fun p => fourierIntegrand M (ν p) (lam p) (x p) (z p) (w p)) := by
  have hzr := modularRoot_measurable.comp hz
  have hwr := modularRoot_measurable.comp hw
  have hzp := modularJacobian_measurable.comp hz
  have hwp := modularJacobian_measurable.comp hw
  unfold fourierIntegrand kernelG5D correction5D_holo
  apply Measurable.mul (by fun_prop)
  apply Measurable.ite (measurableSet_lt hx measurable_const) _ measurable_const
  dsimp
  have hL : Measurable (fun p => ((M * Real.sqrt (2 * (1 - x p)) : ℝ) : ℂ)) := by fun_prop
  have hZ := (hL.mul hzr).mul hwr
  have hExp := Complex.continuous_exp.measurable.comp hZ.neg
  have hCoef : Measurable (fun p =>
    ((M ^ 2 / (32 * Real.pi ^ 2 * Real.sqrt (2 * (1 - x p))) : ℝ) : ℂ)) := by fun_prop
  exact ((measurable_const.mul hzp).mul hwp).mul ((hCoef.mul hExp).mul (hZ.sub_const 2))

theorem fourierG5D_measurable (M : ℝ) :
    Measurable (fun p : ℝ × ℝ × ℝ => fourierG5D M p.1 p.2.1 p.2.2) := by
  have h : Measurable (fun p : ((ℝ × ℝ × ℝ) × ℝ) × ℝ =>
      fourierIntegrand M p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2) :=
    measurable_fourierIntegrand M (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop)
  exact measurable_const.mul
    h.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

theorem fourierG5D_reflect (M ν lam x : ℝ) :
    conj (fourierG5D M ν lam x) = fourierG5D M (-ν) (-lam) x := by
  simp [fourierG5D, fourierIntegrand, ← integral_conj, kernelG5D_conj_real, ← Complex.exp_conj,
    mul_neg, neg_mul, map_ofNat]

private theorem correction5D_holo_differentiable_left (M : ℝ) (w : ℂ) (x : ℝ) :
    DifferentiableOn ℂ (fun z => correction5D_holo M z w x) {z : ℂ | |z.im| < 1 / 2} := by
  unfold correction5D_holo
  have h := modularRoot_differentiableOn
  fun_prop

private theorem fourierIntegrand_differentiable_left (M ν lam x : ℝ) (w : ℂ) :
    DifferentiableOn ℂ (fun z => fourierIntegrand M ν lam x z w) {z : ℂ | |z.im| < 1 / 2} := by
  by_cases hx : x < 1
  · unfold fourierIntegrand kernelG5D
    simp only [ite_eq_left hx]
    have hprime := modularJacobian_differentiableOn
    have hcor := correction5D_holo_differentiable_left M w x
    fun_prop
  · simp only [fourierIntegrand, kernelG5D, ite_eq_right hx, mul_zero]
    exact (differentiable_const (c := (0 : ℂ))).differentiableOn

private theorem fourierIntegrand_differentiable_right (M ν lam x : ℝ) (z : ℂ) :
    DifferentiableOn ℂ (fun w => fourierIntegrand M ν lam x z w) {z : ℂ | |z.im| < 1 / 2} := by
  convert fourierIntegrand_differentiable_left M (-lam) (-ν) x z using 1
  funext w
  rw [fourierIntegrand, fourierIntegrand, kernelG5D_swap M z w x]
  push_cast
  ring_nf

private theorem norm_fourierIntegrand (M ν lam x : ℝ) (z w : ℂ) :
    ‖fourierIntegrand M ν lam x z w‖ = Real.exp (ν * z.im - lam * w.im) * ‖kernelG5D M z w x‖ := by
  rw [fourierIntegrand, norm_mul, Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

/-- A two-sided exponential envelope on the modular radial line. -/
def modularRadialDecay (r : ℝ) : ℝ := Real.exp (-(2 * Real.pi * |r|))

/-- A positive lower bound for the normalized complex logistic denominator. -/
def ModularDenomBound (c : ℝ) : Prop :=
  ∀ z : ℂ, |z.im| ≤ 3 / 8 →
    c * (1 + Real.exp (2 * Real.pi * z.re)) ≤ ‖(1 : ℂ) + Complex.exp (2 * Real.pi * z)‖

private theorem modularDenom_pos {c : ℝ} (hc : 0 < c) (hden : ModularDenomBound c)
    (z : ℂ) (hz : |z.im| ≤ 3 / 8) : 0 < ‖modularDenom z‖ :=
  (mul_pos hc (by positivity)).trans_le (hden z hz)

private theorem norm_modular_exp (a : ℝ) (z : ℂ) :
    ‖Complex.exp ((a : ℂ) * z)‖ = Real.exp (a * z.re) := by
  simp [Complex.norm_exp, Complex.mul_re]

theorem modularRoot_norm_le {c : ℝ} (hc : 0 < c) (hden : ModularDenomBound c)
    (z : ℂ) (hz : |z.im| ≤ 3 / 8) : ‖modularRoot z‖ ≤ 1 / Real.sqrt c := by
  have hN := modularDenom_pos hc hden z hz
  have hcast : (2⁻¹ : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; norm_num
  rw [modularRoot, norm_div, norm_modular_exp, hcast, Complex.norm_cpow_real,
    ← Real.sqrt_eq_rpow]
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hN) (Real.sqrt_pos.2 hc), one_mul,
    show Real.exp (Real.pi * z.re) = √(Real.exp (2 * Real.pi * z.re)) by
      rw [← Real.exp_half]; congr 1; ring,
    ← Real.sqrt_mul (Real.exp_pos _).le]
  apply Real.sqrt_le_sqrt
  rw [mul_comm]
  exact (by nlinarith : c * Real.exp (2 * Real.pi * z.re) ≤
    c * (1 + Real.exp (2 * Real.pi * z.re))).trans (hden z hz)

private theorem modularJacobian_norm_le {c : ℝ} (hc : 0 < c) (hden : ModularDenomBound c)
    (z : ℂ) (hz : |z.im| ≤ 3 / 8) :
    ‖modularJacobian z‖ ≤ (2 * Real.pi / c ^ 2) * modularRadialDecay z.re := by
  let q := Real.exp (2 * Real.pi * z.re)
  have hq : 0 < q := Real.exp_pos _
  have hs : q / (1 + q) ^ 2 ≤ modularRadialDecay z.re := by
    rcases le_or_gt 0 z.re with h | h
    · simp only [modularRadialDecay, abs_of_nonneg h, Real.exp_neg]
      change q / (1 + q) ^ 2 ≤ q⁻¹
      rw [← one_div, le_div_iff₀ hq, div_mul_eq_mul_div, div_le_iff₀ (by positivity), one_mul]
      nlinarith
    · rw [modularRadialDecay, abs_of_neg h,
        show -(2 * Real.pi * -z.re) = 2 * Real.pi * z.re by ring]
      change q / (1 + q) ^ 2 ≤ q
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hq.le (sq_nonneg q), mul_nonneg hq.le hq.le]
  rw [modularJacobian, norm_div, norm_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_pow]
  rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl, norm_modular_exp]
  change 2 * Real.pi * q / ‖modularDenom z‖ ^ 2 ≤ (2 * Real.pi / c ^ 2) * _
  calc
    _ ≤ 2 * Real.pi * q / (c * (1 + q)) ^ 2 := by
      gcongr
      exact hden z hz
    _ = (2 * Real.pi / c ^ 2) * (q / (1 + q) ^ 2) := by rw [mul_pow]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

theorem modularRoot_mul_re_lower {c : ℝ} (hc : 0 < c) (hden : ModularDenomBound c)
    {z w : ℂ} (hz : |z.im| ≤ 3 / 8) (hw : |w.im| ≤ 3 / 8) :
    -(1 / Real.sqrt c * (1 / Real.sqrt c)) ≤ (modularRoot z * modularRoot w).re := by
  have h := (abs_le.mp (Complex.abs_re_le_norm (modularRoot z * modularRoot w))).1
  rw [norm_mul] at h
  refine le_trans (neg_le_neg ?_) h
  exact mul_le_mul (modularRoot_norm_le hc hden z hz) (modularRoot_norm_le hc hden w hw)
    (norm_nonneg _) (by positivity)

private theorem correction5D_holo_norm_le {c : ℝ} (hc : 0 < c) (hden : ModularDenomBound c)
    (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z w : ℂ), |z.im| ≤ 3 / 8 → |w.im| ≤ 3 / 8 →
      ∀ x : ℝ, -1 ≤ x → x < 1 → ‖correction5D_holo M z w x‖ ≤ C * (1 / Real.sqrt (1 - x)) := by
  let R := 1 / Real.sqrt c
  let B := |M| * 2 * R * R
  refine ⟨M ^ 2 / (32 * Real.pi ^ 2) * Real.exp B * (B + 2), by dsimp [B, R]; positivity, ?_⟩
  intro z w hz hw x hx₀ hx₁
  let y := 2 * (1 - x)
  let Z : ℂ := ((M * Real.sqrt y : ℝ) : ℂ) * modularRoot z * modularRoot w
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hZ : ‖Z‖ ≤ B := by
    rw [show ‖Z‖ = |M| * Real.sqrt y * ‖modularRoot z‖ * ‖modularRoot w‖ by
      simp [Z, abs_of_nonneg (Real.sqrt_nonneg y)]]
    have hs : Real.sqrt y ≤ 2 := by
      calc
        _ ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by dsimp [y]; linarith)
        _ = _ := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    exact mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
        (modularRoot_norm_le hc hden z hz) (norm_nonneg _) (by positivity))
      (modularRoot_norm_le hc hden w hw) (norm_nonneg _) (by positivity)
  have he : ‖Complex.exp (-Z)‖ ≤ Real.exp B := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (Complex.abs_re_le_norm Z)).1])
  have hsub : ‖Z - 2‖ ≤ B + 2 :=
    (norm_sub_le _ _).trans (by simpa using add_le_add_right hZ (2 : ℝ))
  change ‖((M ^ 2 / (32 * Real.pi ^ 2 * Real.sqrt y) : ℝ) : ℂ) *
    Complex.exp (-Z) * (Z - 2)‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs : 1 / Real.sqrt y ≤ 1 / Real.sqrt (1 - x) := by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by linarith))
    exact Real.sqrt_le_sqrt (by dsimp [y]; linarith)
  calc
    _ ≤ (M ^ 2 / (32 * Real.pi ^ 2) * (1 / Real.sqrt (1 - x))) * Real.exp B * (B + 2) := by
      rw [← div_div, div_eq_mul_inv _ (Real.sqrt y), ← one_div]
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) he
        (norm_nonneg _) (by positivity)) hsub (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem kernelG5D_norm_le {c : ℝ} (hc : 0 < c) (hden : ModularDenomBound c)
    (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z w : ℂ), |z.im| ≤ 3 / 8 → |w.im| ≤ 3 / 8 →
      ∀ x : ℝ, -1 ≤ x → x < 1 → ‖kernelG5D M z w x‖ ≤
        C * (1 / Real.sqrt (1 - x)) * modularRadialDecay z.re * modularRadialDecay w.re := by
  obtain ⟨C, hC, hcor⟩ := correction5D_holo_norm_le hc hden M
  let J := 2 * Real.pi / c ^ 2
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨4 * J ^ 2 * C + 1, by positivity, ?_⟩
  intro z w hz hw x hx₀ hx₁
  rw [kernelG5D, ite_eq_left hx₁, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ (4 * (J * modularRadialDecay z.re) * (J * modularRadialDecay w.re)) *
          (C * (1 / Real.sqrt (1 - x))) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (modularJacobian_norm_le hc hden z hz)
        (by norm_num)) (modularJacobian_norm_le hc hden w hw)
        (norm_nonneg _) (by unfold modularRadialDecay; positivity))
        (hcor z w hz hw x hx₀ hx₁) (norm_nonneg _) (by unfold modularRadialDecay; positivity)
    _ = (4 * J ^ 2 * C) * (1 / Real.sqrt (1 - x)) *
          modularRadialDecay z.re * modularRadialDecay w.re := by ring
    _ ≤ _ := by gcongr <;> first | linarith | (unfold modularRadialDecay; positivity)

private def contourLine (r y : ℝ) : ℂ := (r : ℂ) + (y : ℂ) * Complex.I

@[simp] private theorem contourLine_re (r y : ℝ) : (contourLine r y).re = r := by
  simp [contourLine, Complex.mul_re]

@[simp] private theorem contourLine_im (r y : ℝ) : (contourLine r y).im = y := by
  simp [contourLine, Complex.mul_im]

@[simp] private theorem contourLine_zero (r : ℝ) : contourLine r 0 = (r : ℂ) := by
  simp [contourLine]

private theorem radialDecay_nonneg (r : ℝ) : 0 ≤ modularRadialDecay r :=
  (Real.exp_pos _).le

private theorem fourierIntegrand_line_le {C M ν lam x : ℝ}
    (hG : ∀ z w : ℂ, |z.im| ≤ 3 / 8 → |w.im| ≤ 3 / 8 →
      ‖kernelG5D M z w x‖ ≤ C * modularRadialDecay z.re * modularRadialDecay w.re)
    {y t : ℝ} (hy : |y| ≤ 3 / 8) (ht : |t| ≤ 3 / 8) (r s : ℝ) :
    ‖fourierIntegrand M ν lam x (contourLine r y) (contourLine s t)‖ ≤
      (C * Real.exp (ν * y - lam * t)) * modularRadialDecay r * modularRadialDecay s := by
  rw [norm_fourierIntegrand, contourLine_im, contourLine_im]
  calc
    _ ≤ Real.exp (ν * y - lam * t) * (C * modularRadialDecay r * modularRadialDecay s) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa using hG (contourLine r y) (contourLine s t) (by simpa using hy) (by simpa using ht)
    _ = _ := by ring

private theorem fourierIntegrand_line_integrable (hd : Integrable modularRadialDecay)
    {C M ν lam x : ℝ}
    (hG : ∀ z w : ℂ, |z.im| ≤ 3 / 8 → |w.im| ≤ 3 / 8 →
      ‖kernelG5D M z w x‖ ≤ C * modularRadialDecay z.re * modularRadialDecay w.re)
    {y t : ℝ} (hy : |y| ≤ 3 / 8) (ht : |t| ≤ 3 / 8) :
    Integrable (fun p : ℝ × ℝ => fourierIntegrand M ν lam x
      (contourLine p.1 y) (contourLine p.2 t)) ((volume : Measure ℝ).prod volume) := by
  apply ((hd.const_mul (C * Real.exp (ν * y - lam * t))).mul_prod hd).mono'
  · apply Measurable.aestronglyMeasurable
    exact measurable_fourierIntegrand M measurable_const measurable_const measurable_const
      (by unfold contourLine; fun_prop) (by unfold contourLine; fun_prop)
  · exact ae_of_all _ fun p => fourierIntegrand_line_le hG hy ht p.1 p.2

private theorem fourierIntegrand_swap (M ν lam x : ℝ) (z w : ℂ) :
    fourierIntegrand M (-ν) (-lam) x z w = fourierIntegrand M lam ν x w z := by
  rw [fourierIntegrand, fourierIntegrand, kernelG5D_swap M z w x]
  push_cast
  congr 2
  ring

/-- Hermitian symmetry follows by exchanging the radial integrals after complex conjugation. -/
theorem fourierG5D_conj_swap {c : ℝ} (hc : 0 < c) (hden : ModularDenomBound c)
    (hd : Integrable modularRadialDecay) (M ν lam x : ℝ) (hx : -1 ≤ x) :
    conj (fourierG5D M ν lam x) = fourierG5D M lam ν x := by
  by_cases hx₁ : x < 1
  · obtain ⟨C, _, hC⟩ := kernelG5D_norm_le hc hden M
    have h0 : |(0 : ℝ)| ≤ 3 / 8 := by norm_num
    have hG (z w : ℂ) (hz : |z.im| ≤ 3 / 8) (hw : |w.im| ≤ 3 / 8) :=
      hC z w hz hw x hx hx₁
    rw [fourierG5D_reflect, fourierG5D, fourierG5D]
    congr 1
    rw [integral_integral_swap
      (show Integrable (Function.uncurry (fun r s : ℝ => fourierIntegrand M (-ν) (-lam) x r s))
        ((volume : Measure ℝ).prod volume) by
        change Integrable (fun p : ℝ × ℝ => fourierIntegrand M (-ν) (-lam) x p.1 p.2) _
        simpa using fourierIntegrand_line_integrable
          (ν := -ν) (lam := -lam) hd hG h0 h0)]
    simp_rw [fourierIntegrand_swap]
  · rw [fourierG5D_zero M ν lam (le_of_not_gt hx₁), fourierG5D_zero M lam ν (le_of_not_gt hx₁),
      map_zero]

private theorem strip_phase_le (ν lam : ℝ) (z w : ℂ)
    (hz : |z.im| ≤ 3 / 8) (hw : |w.im| ≤ 3 / 8) :
    ν * z.im - lam * w.im ≤ (3 / 8 : ℝ) * (|ν| + |lam|) := by
  have hν : ν * z.im ≤ |ν| * (3 / 8) := calc
    ν * z.im ≤ |ν * z.im| := le_abs_self _
    _ = |ν| * |z.im| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have hlam : -(lam * w.im) ≤ |lam| * (3 / 8) := calc
    -(lam * w.im) ≤ |lam * w.im| := neg_le_abs _
    _ = |lam| * |w.im| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  linarith

private def contourHeight (ν : ℝ) : ℝ := if 0 ≤ ν then -(3 / 8) else 3 / 8

private theorem contourHeight_abs (ν : ℝ) : |contourHeight ν| ≤ 3 / 8 := by
  by_cases hν : 0 ≤ ν <;> norm_num [contourHeight, hν]

private theorem contourHeight_mul (ν : ℝ) : ν * contourHeight ν = -(3 / 8 : ℝ) * |ν| := by
  by_cases hν : 0 ≤ ν
  · simp [contourHeight, hν, abs_of_nonneg hν]; ring
  · simp [contourHeight, hν, abs_of_neg (lt_of_not_ge hν)]; ring

/-- Consecutive horizontal contour shifts give the uniform off-diagonal Fourier bound.
The one-variable Cauchy shift applies to the exponential envelopes of the two slices. -/
theorem fourierG5D_bound_of_horizontal_shift {c : ℝ} (hc : 0 < c)
    (hden : ModularDenomBound c) (hd : Integrable modularRadialDecay)
    (hShift : ∀ (f : ℂ → ℂ) (B : ℝ), 0 ≤ B →
      DifferentiableOn ℂ f {z : ℂ | |z.im| < 1 / 2} →
      (∀ z : ℂ, |z.im| ≤ 3 / 8 →
        ‖f z‖ ≤ B * Real.exp (-(2 * Real.pi * |z.re|)) * (1 + |z.re|)) →
      ∀ y : ℝ, |y| ≤ 3 / 8 →
        (∫ r : ℝ, f (r : ℂ)) = ∫ r : ℝ, f ((r : ℂ) + (y : ℂ) * Complex.I))
    (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν lam x : ℝ), -1 ≤ x → x < 1 →
      ‖fourierG5D M ν lam x‖ ≤ C * Real.exp (-(3 / 8 : ℝ) * (|ν| + |lam|)) *
        (1 / Real.sqrt (1 - x)) := by
  obtain ⟨C, hC, hbound⟩ := kernelG5D_norm_le hc hden M
  let J := ∫ r : ℝ, modularRadialDecay r
  refine ⟨‖(1 / (2 * (Real.pi : ℂ)))‖ * C * (1 + J ^ 2) + 1, by positivity, ?_⟩
  intro ν lam x hx₀ hx₁
  let F := fourierIntegrand M ν lam x
  let y := contourHeight ν
  let t := -contourHeight lam
  have h0 : |(0 : ℝ)| ≤ 3 / 8 := by norm_num
  have hy : |y| ≤ 3 / 8 := contourHeight_abs ν
  have ht : |t| ≤ 3 / 8 := by simpa [t] using contourHeight_abs lam
  let K := C * (1 / Real.sqrt (1 - x))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG (z w : ℂ) (hz : |z.im| ≤ 3 / 8) (hw : |w.im| ≤ 3 / 8) :
      ‖kernelG5D M z w x‖ ≤ K * modularRadialDecay z.re * modularRadialDecay w.re :=
    hbound z w hz hw x hx₀ hx₁
  let A := K * Real.exp ((3 / 8 : ℝ) * (|ν| + |lam|))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmajor (z w : ℂ) (hz : |z.im| ≤ 3 / 8) (hw : |w.im| ≤ 3 / 8) :
      ‖F z w‖ ≤ A * modularRadialDecay z.re * modularRadialDecay w.re := by
    rw [norm_fourierIntegrand]
    calc
      _ ≤ Real.exp (ν * z.im - lam * w.im) *
          (K * modularRadialDecay z.re * modularRadialDecay w.re) :=
        mul_le_mul_of_nonneg_left (hG z w hz hw) (Real.exp_pos _).le
      _ ≤ _ := by
        rw [show A * modularRadialDecay z.re * modularRadialDecay w.re =
          Real.exp ((3 / 8 : ℝ) * (|ν| + |lam|)) *
            (K * modularRadialDecay z.re * modularRadialDecay w.re) by dsimp [A]; ring]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (strip_phase_le ν lam z w hz hw))
          (by unfold modularRadialDecay; positivity)
  have hshiftLeft (s : ℝ) : (∫ r : ℝ, F r s) = ∫ r : ℝ, F (contourLine r y) s := by
    apply hShift _ (A * modularRadialDecay s)
      (mul_nonneg hA (radialDecay_nonneg s))
      (fourierIntegrand_differentiable_left M ν lam x s) _ y hy
    intro z hz
    have hb := hmajor z (s : ℂ) hz (by simpa using h0)
    calc
      _ ≤ (A * modularRadialDecay s) * modularRadialDecay z.re := by
        simpa only [Complex.ofReal_re, mul_assoc, mul_comm, mul_left_comm] using hb
      _ ≤ _ := by
        unfold modularRadialDecay
        exact le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (abs_nonneg _))
  have hshiftRight (r : ℝ) :
      (∫ s : ℝ, F (contourLine r y) s) = ∫ s : ℝ, F (contourLine r y) (contourLine s t) := by
    apply hShift _ (A * modularRadialDecay r)
      (mul_nonneg hA (radialDecay_nonneg r))
      (fourierIntegrand_differentiable_right M ν lam x (contourLine r y)) _ t ht
    intro w hw
    have hb := hmajor (contourLine r y) w (by simpa using hy) hw
    calc
      _ ≤ (A * modularRadialDecay r) * modularRadialDecay w.re := by simpa using hb
      _ ≤ _ := by
        unfold modularRadialDecay
        exact le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (abs_nonneg _))
  have hshift : (∫ r : ℝ, ∫ s : ℝ, F r s) =
      ∫ r : ℝ, ∫ s : ℝ, F (contourLine r y) (contourLine s t) := calc
    _ = ∫ s : ℝ, ∫ r : ℝ, F r s :=
      integral_integral_swap (show Integrable (Function.uncurry (fun r s : ℝ => F r s))
        ((volume : Measure ℝ).prod volume) by
          change Integrable (fun p : ℝ × ℝ => F p.1 p.2) _
          simpa [F] using fourierIntegrand_line_integrable
            (ν := ν) (lam := lam) hd hG h0 h0)
    _ = ∫ s : ℝ, ∫ r : ℝ, F (contourLine r y) s := by simp_rw [hshiftLeft]
    _ = ∫ r : ℝ, ∫ s : ℝ, F (contourLine r y) s :=
      (integral_integral_swap
        (show Integrable (Function.uncurry (fun r s : ℝ => F (contourLine r y) s))
          ((volume : Measure ℝ).prod volume) by
            change Integrable (fun p : ℝ × ℝ => F (contourLine p.1 y) p.2) _
            simpa [F] using fourierIntegrand_line_integrable
              (ν := ν) (lam := lam) hd hG hy h0)).symm
    _ = _ := by simp_rw [hshiftRight]
  have hphase : ν * y - lam * t = -(3 / 8 : ℝ) * (|ν| + |lam|) := by
    dsimp [y, t]
    rw [mul_neg, contourHeight_mul, contourHeight_mul]
    ring
  let D := K * Real.exp (ν * y - lam * t)
  have hnorm : ‖∫ r : ℝ, ∫ s : ℝ, F (contourLine r y) (contourLine s t)‖ ≤ D * J ^ 2 := by
    rw [← integral_prod _ (fourierIntegrand_line_integrable (ν := ν) (lam := lam) hd hG hy ht)]
    calc
      _ ≤ ∫ p : ℝ × ℝ, D * modularRadialDecay p.1 * modularRadialDecay p.2
          ∂((volume : Measure ℝ).prod volume) :=
        norm_integral_le_of_norm_le ((hd.const_mul D).mul_prod hd)
          (ae_of_all _ fun p => fourierIntegrand_line_le hG hy ht p.1 p.2)
      _ = _ := by
        rw [integral_prod_mul (fun r => D * modularRadialDecay r) modularRadialDecay,
          integral_const_mul]
        dsimp [J]
        ring
  change ‖(1 / (2 * (Real.pi : ℂ))) * ∫ r : ℝ, ∫ s : ℝ, F r s‖ ≤ _
  rw [hshift, norm_mul]
  calc
    _ ≤ ‖(1 / (2 * (Real.pi : ℂ)))‖ * (D * J ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = (‖(1 / (2 * (Real.pi : ℂ)))‖ * C * J ^ 2) *
          Real.exp (-(3 / 8 : ℝ) * (|ν| + |lam|)) * (1 / Real.sqrt (1 - x)) := by
      dsimp [D, K]
      rw [hphase]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le) (by positivity)
      nlinarith [mul_nonneg (norm_nonneg (1 / (2 * (Real.pi : ℂ)))) hC.le]

end Omega
