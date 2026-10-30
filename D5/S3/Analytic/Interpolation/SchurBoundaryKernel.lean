/- GID: D5/S3/Analytic/Interpolation/SchurBoundaryKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SchurBoundaryKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.FunctionSeries, mathlib/module/Mathlib.Analysis.PSeries, mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic]
   utility: none
   digest: The real Fourier kernel for an imaginary-axis divided difference. -/

import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The actual Fourier kernel and its closed-domain analytic controls. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Analytic.Interpolation.SchurBoundaryKernel

/-- The actual odd cosine series of the imaginary-axis primitive average. -/
def boundaryTerm (b θ : ℝ) (j : ℕ) : ℝ :=
  2 * ((-1 : ℝ) ^ (j + 1) * b ^ (2 * j + 2)) /
    ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3)) * Real.cos ((2 * (j : ℝ) + 1) * θ)

def boundaryKernel (b θ : ℝ) : ℝ := ∑' j : ℕ, boundaryTerm b θ j

private def majorant (j : ℕ) : ℝ :=
  2 / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))

private theorem majorant_summable : Summable majorant := by
  have hs : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply Summable.of_nonneg_of_le (fun j => by dsimp [majorant]; positivity) _ hs
  intro j
  dsimp [majorant]
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

private theorem term_norm_le {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (θ : ℝ) (j : ℕ) :
    ‖boundaryTerm b θ j‖ ≤ majorant j := by
  have hp : |b ^ (2 * j + 2)| ≤ 1 := by
    rw [abs_pow, abs_of_nonneg hb.1]
    exact pow_le_one₀ hb.1 hb.2
  have hc := Real.abs_cos_le_one ((2 * (j : ℝ) + 1) * θ)
  rw [Real.norm_eq_abs]
  dsimp [boundaryTerm, majorant]
  rw [abs_mul, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < (2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))]
  calc
    _ ≤ (2 * 1 / ((2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 3))) * 1 :=
      mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num))
        (by positivity)) hc (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem kernel_continuous {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    Continuous (boundaryKernel b) := by
  exact continuous_tsum (fun j => by unfold boundaryTerm; fun_prop)
    majorant_summable (fun j θ => term_norm_le hb θ j)

private theorem kernel_uniform_convergence :
    TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => ∑ j ∈ Finset.range n, boundaryTerm p.1 p.2 j)
      (fun p => boundaryKernel p.1 p.2) atTop {p | p.1 ∈ Icc (0 : ℝ) 1} :=
  tendstoUniformlyOn_tsum_nat majorant_summable (fun j p hp => term_norm_le hp p.2 j)

private theorem kernel_reflection (b θ : ℝ) :
    boundaryKernel b (Real.pi - θ) = -boundaryKernel b θ := by
  unfold boundaryKernel
  rw [← tsum_neg]
  apply tsum_congr
  intro j
  have hc : Real.cos ((2 * (j : ℝ) + 1) * (Real.pi - θ)) =
      -Real.cos ((2 * (j : ℝ) + 1) * θ) := by
    have he : (2 * (j : ℝ) + 1) * (Real.pi - θ) =
        ((2 * j + 1 : ℕ) : ℝ) * Real.pi - (2 * (j : ℝ) + 1) * θ := by push_cast; ring
    rw [he, Real.cos_nat_mul_pi_sub]
    norm_num [pow_add, pow_mul]
  simp only [boundaryTerm, hc, mul_neg]

private theorem rational_cosine_real (q θ : ℝ) :
    (Complex.exp ((θ : ℂ) * Complex.I) /
      (1 - (-(q : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ^ 2))).re =
      Real.cos θ * (1 + q) / ((1 - q) ^ 2 + 4 * q * Real.cos θ ^ 2) := by
  let u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  change (u / (1 - (-(q : ℂ) * u ^ 2))).re = _
  have huR : u.re = Real.cos θ := by
    dsimp [u]
    exact Complex.exp_ofReal_mul_I_re θ
  have huI : u.im = Real.sin θ := by
    dsimp [u]
    exact Complex.exp_ofReal_mul_I_im θ
  have hdR : (1 - -(q : ℂ) * u ^ 2).re =
      1 + q * (Real.cos θ ^ 2 - Real.sin θ ^ 2) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im, huR, huI]
  have hdI : (1 - -(q : ℂ) * u ^ 2).im =
      2 * q * Real.cos θ * Real.sin θ := by
    simp [pow_two, Complex.mul_re, Complex.mul_im, huR, huI]
    ring
  have htrig := Real.sin_sq_add_cos_sq θ
  have hN : u.re * (1 - -(q : ℂ) * u ^ 2).re +
      u.im * (1 - -(q : ℂ) * u ^ 2).im = Real.cos θ * (1 + q) := by
    rw [huR, huI, hdR, hdI]
    linear_combination q * Real.cos θ * htrig
  have hD : Complex.normSq (1 - -(q : ℂ) * u ^ 2) =
      (1 - q) ^ 2 + 4 * q * Real.cos θ ^ 2 := by
    rw [Complex.normSq_apply, hdR, hdI]
    linear_combination
      (-2 * q + q ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2 + 1)) * htrig
  rw [Complex.div_re, ← add_div, hN, hD]

private theorem cosine_geometric (q θ : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun j : ℕ => (-q) ^ j * Real.cos ((2 * (j : ℝ) + 1) * θ))
      (Real.cos θ * (1 + q) / ((1 - q) ^ 2 + 4 * q * (Real.cos θ) ^ 2)) := by
  let u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hr : ‖-(q : ℂ) * u ^ 2‖ < 1 := by
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0,
      norm_pow, hu, one_pow, mul_one]
    exact hq1
  have hh := Complex.reCLM.hasSum
    ((hasSum_geometric_of_norm_lt_one hr).mul_left u)
  have he (j : ℕ) :
      (u * (-(q : ℂ) * u ^ 2) ^ j).re =
        (-q) ^ j * Real.cos ((2 * (j : ℝ) + 1) * θ) := by
    have hp : u * (-(q : ℂ) * u ^ 2) ^ j = (-q : ℂ) ^ j * u ^ (2 * j + 1) := by
      rw [mul_pow, ← pow_mul, pow_succ]
      ring
    have hex : (u ^ (2 * j + 1)).re = Real.cos ((2 * (j : ℝ) + 1) * θ) := by
      rw [show u ^ (2 * j + 1) =
        Complex.exp ((((2 * j + 1 : ℕ) : ℂ) * θ) * Complex.I) by
          rw [mul_assoc, Complex.exp_nat_mul]]
      simpa using
          Complex.exp_ofReal_mul_I_re ((2 * (j : ℝ) + 1) * θ)
    rw [hp]
    simpa only [← Complex.ofReal_neg, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      congrArg (fun x : ℝ => (-q) ^ j * x) hex
  change HasSum (fun j : ℕ => (u * (-(q : ℂ) * u ^ 2) ^ j).re)
    ((u * (1 - (-(q : ℂ) * u ^ 2))⁻¹).re) at hh
  simp_rw [he] at hh
  convert hh using 1
  rw [← div_eq_mul_inv]
  exact (rational_cosine_real q θ).symm


private def densityTerm (b θ : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  -2 * b ^ 2 * (-b ^ 2) ^ j * Real.cos ((2 * (j : ℝ) + 1) * θ) *
    (t ^ (2 * j + 1) * (1 - t))

private theorem density_integral (b θ : ℝ) (j : ℕ) :
    (∫ t in (0 : ℝ)..1, densityTerm b θ j t) = boundaryTerm b θ j := by
  unfold densityTerm
  rw [intervalIntegral.integral_const_mul]
  have he : (fun t : ℝ => t ^ (2 * j + 1) * (1 - t)) =
      (fun t => t ^ (2 * j + 1) - t ^ (2 * j + 2)) := by
    funext t
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, pow_succ]
    ring
  rw [he, intervalIntegral.integral_sub
    ((show Continuous (fun t : ℝ => t ^ (2 * j + 1)) by fun_prop).intervalIntegrable 0 1)
    ((show Continuous (fun t : ℝ => t ^ (2 * j + 2)) by fun_prop).intervalIntegrable 0 1),
    integral_pow, integral_pow]
  simp only [one_pow, zero_pow (by omega : 2 * j + 1 + 1 ≠ 0),
    zero_pow (by omega : 2 * j + 2 + 1 ≠ 0), sub_zero]
  unfold boundaryTerm
  push_cast
  rw [show -b ^ 2 = (-1 : ℝ) * b ^ 2 by ring, mul_pow, ← pow_mul,
    pow_add]
  simp only [pow_add, pow_one]
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  field_simp
  <;> ring

private theorem kernel_integral_interior (b θ : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    boundaryKernel b θ = -2 * b ^ 2 * Real.cos θ *
      ∫ t in (0 : ℝ)..1, t * (1 - t) * (1 + b ^ 2 * t ^ 2) /
        ((1 - b ^ 2 * t ^ 2) ^ 2 + 4 * b ^ 2 * t ^ 2 * Real.cos θ ^ 2) := by
  have hb2 : b ^ 2 < 1 := by nlinarith
  let U : ℕ → ℝ := fun j => 2 * b ^ 2 * (b ^ 2) ^ j
  have hU : Summable U :=
    (summable_geometric_of_lt_one (sq_nonneg b) hb2).mul_left _
  let R : ℝ → ℝ := fun t => -2 * b ^ 2 * Real.cos θ *
    (t * (1 - t) * (1 + b ^ 2 * t ^ 2) /
      ((1 - b ^ 2 * t ^ 2) ^ 2 + 4 * b ^ 2 * t ^ 2 * Real.cos θ ^ 2))
  have hlim (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      HasSum (fun j => densityTerm b θ j t) (R t) := by
    have hq : b ^ 2 * t ^ 2 < 1 := by
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      nlinarith [sq_nonneg b, sq_nonneg t]
    convert (cosine_geometric (b ^ 2 * t ^ 2) θ (by positivity) hq).mul_left
      (-2 * b ^ 2 * t * (1 - t)) using 1
    · funext j
      dsimp [densityTerm]
      rw [show -(b ^ 2 * t ^ 2) = (-b ^ 2) * t ^ 2 by ring,
        mul_pow, ← pow_mul, pow_succ]
      ring
    · dsimp [R]
      ring
  have hbound (j : ℕ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      ‖densityTerm b θ j t‖ ≤ U j := by
    have ht0 : 0 ≤ t := ht.1.le
    have htP : |t ^ (2 * j + 1)| ≤ 1 := by
      rw [abs_pow, abs_of_nonneg ht0]
      exact pow_le_one₀ ht0 ht.2
    have hsub : |1 - t| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]
      linarith [ht.1]
    have hc := Real.abs_cos_le_one ((2 * (j : ℝ) + 1) * θ)
    dsimp [densityTerm, U]
    simp only [abs_mul, abs_pow, abs_neg, abs_of_nonneg (sq_nonneg b),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg ht0]
    have htP' : t ^ (2 * j + 1) ≤ 1 := pow_le_one₀ ht0 ht.2
    calc
      _ ≤ 2 * b ^ 2 * (b ^ 2) ^ j * 1 * (1 * 1) := by gcongr
      _ = _ := by ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := (1 : ℝ)) (F := densityTerm b θ) (f := R)
    (fun j (_ : ℝ) => U j)
    (fun j => (show Continuous (densityTerm b θ j) by
      unfold densityTerm; fun_prop).aestronglyMeasurable)
    (fun j => .of_forall (fun t ht => hbound j t (by simpa using ht)))
    (.of_forall (fun _ _ => hU)) intervalIntegrable_const
    (.of_forall (fun t ht => hlim t (by simpa using ht)))
  simp_rw [density_integral] at hsum
  calc
    boundaryKernel b θ = ∫ t in (0 : ℝ)..1, R t := hsum.tsum_eq
    _ = _ := by dsimp [R]; rw [intervalIntegral.integral_const_mul]

private theorem kernel_sign_interior (b θ : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Real.cos θ * boundaryKernel b θ ≤ 0 := by
  rw [kernel_integral_interior b θ hb0 hb1]
  have hi : 0 ≤ ∫ t in (0 : ℝ)..1,
      t * (1 - t) * (1 + b ^ 2 * t ^ 2) /
        ((1 - b ^ 2 * t ^ 2) ^ 2 + 4 * b ^ 2 * t ^ 2 * Real.cos θ ^ 2) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    exact div_nonneg (by positivity [ht.1, sub_nonneg.mpr ht.2]) (by positivity)
  nlinarith [sq_nonneg (Real.cos θ), sq_nonneg b,
    mul_nonneg (mul_nonneg (sq_nonneg b) (sq_nonneg (Real.cos θ))) hi]

private theorem term_integral_zero (b : ℝ) (j : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), boundaryTerm b θ j) = 0 := by
  unfold boundaryTerm
  rw [intervalIntegral.integral_const_mul]
  have hk : 2 * (j : ℝ) + 1 ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left Real.cos hk, integral_cos]
  have he : (2 * (j : ℝ) + 1) * (2 * Real.pi) =
      ((4 * j + 2 : ℕ) : ℝ) * Real.pi := by push_cast; ring
  have hs : Real.sin ((2 * (j : ℝ) + 1) * (2 * Real.pi)) = 0 := by
    rw [he]
    exact Real.sin_nat_mul_pi (4 * j + 2)
  simp only [mul_zero, Real.sin_zero, hs, sub_zero, smul_zero, zero_mul]

private theorem kernel_mean_zero {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), boundaryKernel b θ) = 0 := by
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := (2 * Real.pi))
    (F := fun j θ => boundaryTerm b θ j) (f := boundaryKernel b)
    (fun j (_ : ℝ) => majorant j)
    (fun j => (show Continuous (fun θ => boundaryTerm b θ j) by
      unfold boundaryTerm; fun_prop).aestronglyMeasurable)
    (fun j => .of_forall (fun θ _ => term_norm_le hb θ j))
    (.of_forall (fun _ _ => majorant_summable)) intervalIntegrable_const
    (.of_forall (fun θ _ =>
      ((majorant_summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (term_norm_le hb θ)).of_norm).hasSum))
  simp_rw [term_integral_zero] at hsum
  simpa using hsum.tsum_eq.symm

private def kernelQ (t c : ℝ) : ℝ :=
  2 * c * t * (1 + t ^ 2) / ((1 - t ^ 2) ^ 2 + 4 * c ^ 2 * t ^ 2)

private theorem kernelQ_den_pos {t c : ℝ} (hc : 0 < c) :
    0 < (1 - t ^ 2) ^ 2 + 4 * c ^ 2 * t ^ 2 := by
  by_cases ht : t = 0
  · simp [ht]
  · have h : 0 < 4 * c ^ 2 * t ^ 2 := by positivity
    nlinarith [sq_nonneg (1 - t ^ 2)]

private theorem kernelQ_nonneg {t c : ℝ} (ht : 0 ≤ t) (hc : 0 < c) :
    0 ≤ kernelQ t c := div_nonneg (by positivity) (kernelQ_den_pos hc).le

private theorem kernelQ_small {t c : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 3))
    (hc : c ∈ Ioc (0 : ℝ) 1) : kernelQ t c ≤ 2 * t / (1 + t ^ 2) := by
  have h1 : 0 ≤ 1 - t ^ 2 - 2 * t := by nlinarith [ht.1, ht.2]
  have h2 : 0 ≤ (1 - t ^ 2) ^ 2 - 4 * c * t ^ 2 := by
    nlinarith [sq_nonneg (1 - t ^ 2 - 2 * t),
      mul_nonneg h1 (by nlinarith [ht.1] : 0 ≤ 1 - t ^ 2 + 2 * t),
      mul_nonneg (sub_nonneg.mpr hc.2) (sq_nonneg t)]
  have h3 := mul_nonneg (sub_nonneg.mpr hc.2) h2
  have h4 := mul_nonneg ht.1 h3
  unfold kernelQ
  apply (div_le_div_iff₀ (kernelQ_den_pos hc.1) (by positivity)).mpr
  nlinarith

private def smallEnvelope (t : ℝ) : ℝ := 2 * t * (1 - t) * (1 - (9 / 10) * t ^ 2)
private def largeEnvelope (t : ℝ) : ℝ :=
  3 / 8 + t / 8 - (3 / 16) * (t - 1 / 3) * (1 - t)

private theorem kernelQ_small_envelope {t c : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 / 3)) (hc : c ∈ Ioc (0 : ℝ) 1) :
    (1 - t) * kernelQ t c ≤ smallEnvelope t := by
  have ht1 : t ≤ 1 := ht.2.trans (by norm_num)
  have h := mul_le_mul_of_nonneg_left (kernelQ_small ht hc) (sub_nonneg.mpr ht1)
  apply h.trans
  unfold smallEnvelope
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)).mpr
  have hpoly : 0 ≤ t ^ 2 * (1 - 9 * t ^ 2) := by
    apply mul_nonneg (sq_nonneg t)
    nlinarith [ht.1, ht.2]
  have hmul := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht1)) hpoly
  nlinarith

private theorem kernelQ_large_envelope {t c : ℝ}
    (ht : t ∈ Icc (1 / 3 : ℝ) 1) (hc : c ∈ Ioc (0 : ℝ) 1) :
    (1 - t) * kernelQ t c ≤ largeEnvelope t := by
  have ht0 : 0 ≤ t := (by norm_num : (0 : ℝ) ≤ 1 / 3).trans ht.1
  have hfirst : (1 - t) * kernelQ t c ≤ (1 + t ^ 2) / (2 * (1 + t)) := by
    unfold kernelQ
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (kernelQ_den_pos hc.1) (by positivity)).mpr
    have h := mul_nonneg (show 0 ≤ 1 + t ^ 2 by positivity)
      (sq_nonneg (1 - t ^ 2 - 2 * c * t))
    nlinarith
  apply hfirst.trans
  apply (div_le_iff₀ (by positivity : 0 < 2 * (1 + t))).mpr
  unfold largeEnvelope
  have h := mul_nonneg (by linarith [ht.1] : 0 ≤ 3 * t - 1) (sq_nonneg (t - 1))
  nlinarith

private theorem envelope_integrals :
    (∫ t in (0 : ℝ)..(1 / 3), smallEnvelope t) = 667 / 8100 ∧
    (∫ t in (1 / 3 : ℝ)..1, largeEnvelope t) = 8 / 27 := by
  constructor
  · have hd (t : ℝ) : HasDerivAt
        (fun t : ℝ => t ^ 2 - (2 / 3) * t ^ 3 - (9 / 20) * t ^ 4 + (9 / 25) * t ^ 5)
        (smallEnvelope t) t := by
      convert! ((((hasDerivAt_id t).pow 2).sub
        (((hasDerivAt_id t).pow 3).const_mul (2 / 3))).sub
        (((hasDerivAt_id t).pow 4).const_mul (9 / 20))).add
        (((hasDerivAt_id t).pow 5).const_mul (9 / 25)) using 1 <;>
        first
        | (funext y
           change y ^ 2 - (2 / 3) * y ^ 3 - (9 / 20) * y ^ 4 + (9 / 25) * y ^ 5 =
             y ^ 2 - y ^ 3 * (2 / 3) - y ^ 4 * (9 / 20) + y ^ 5 * (9 / 25)
           ring)
        | (dsimp [smallEnvelope]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((show Continuous smallEnvelope by unfold smallEnvelope; fun_prop).intervalIntegrable _ _)]
    norm_num
  · have hd (t : ℝ) : HasDerivAt
        (fun t : ℝ => (7 / 16) * t - (1 / 16) * t ^ 2 + (1 / 16) * t ^ 3)
        (largeEnvelope t) t := by
      convert! (((hasDerivAt_id t).const_mul (7 / 16)).sub
        (((hasDerivAt_id t).pow 2).const_mul (1 / 16))).add
        (((hasDerivAt_id t).pow 3).const_mul (1 / 16)) using 1 <;>
        first
        | (funext y
           change (7 / 16) * y - (1 / 16) * y ^ 2 + (1 / 16) * y ^ 3 =
             y * (7 / 16) - y ^ 2 * (1 / 16) + y ^ 3 * (1 / 16)
           ring)
        | (dsimp [largeEnvelope]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((show Continuous largeEnvelope by unfold largeEnvelope; fun_prop).intervalIntegrable _ _)]
    norm_num

private theorem kernelQ_continuous {c : ℝ} (hc : 0 < c) :
    Continuous (fun t => kernelQ t c) := by
  unfold kernelQ
  exact (by fun_prop : Continuous (fun t : ℝ => 2 * c * t * (1 + t ^ 2))).div
    (by fun_prop) (fun t => (kernelQ_den_pos hc).ne')

private theorem kernelQ_integral_bound {c : ℝ} (hc : c ∈ Ioc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, (1 - t) * kernelQ t c) ≤ 3067 / 8100 := by
  have hcont : Continuous (fun t : ℝ => (1 - t) * kernelQ t c) := by
    exact (continuous_const.sub continuous_id).mul (kernelQ_continuous hc.1)
  have hsmall := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (hcont.intervalIntegrable 0 (1 / 3))
    ((show Continuous smallEnvelope by unfold smallEnvelope; fun_prop).intervalIntegrable _ _)
    (fun t ht => kernelQ_small_envelope ht hc)
  have hlarge := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 / 3 : ℝ) ≤ 1)
    (hcont.intervalIntegrable (1 / 3) 1)
    ((show Continuous largeEnvelope by unfold largeEnvelope; fun_prop).intervalIntegrable _ _)
    (fun t ht => kernelQ_large_envelope ht hc)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 (1 / 3)) (hcont.intervalIntegrable (1 / 3) 1)]
  rw [envelope_integrals.1] at hsmall
  rw [envelope_integrals.2] at hlarge
  linarith

private theorem kernel_size_interior (b θ : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    |boundaryKernel b θ| ≤ 3067 / 8100 := by
  by_cases hb : b = 0
  · norm_num [boundaryKernel, boundaryTerm, hb]
  have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hb)
  by_cases hz : Real.cos θ = 0
  · rw [kernel_integral_interior b θ hb0 hb1, hz]
    norm_num
  let c := |Real.cos θ|
  have hc : c ∈ Ioc (0 : ℝ) 1 := ⟨abs_pos.mpr hz, Real.abs_cos_le_one θ⟩
  have hden (t : ℝ) :
      (1 - (b * t) ^ 2) ^ 2 + 4 * c ^ 2 * (b * t) ^ 2 =
        (1 - b ^ 2 * t ^ 2) ^ 2 + 4 * b ^ 2 * t ^ 2 * Real.cos θ ^ 2 := by
    dsimp [c]
    rw [sq_abs]
    ring
  have hi : 0 ≤ ∫ t in (0 : ℝ)..1,
      t * (1 - t) * (1 + b ^ 2 * t ^ 2) /
        ((1 - b ^ 2 * t ^ 2) ^ 2 + 4 * b ^ 2 * t ^ 2 * Real.cos θ ^ 2) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    apply div_nonneg
    · positivity [ht.1, sub_nonneg.mpr ht.2]
    · positivity
  have hrep : |boundaryKernel b θ| =
      ∫ t in (0 : ℝ)..1, b * (1 - t) * kernelQ (b * t) c := by
    rw [kernel_integral_interior b θ hb0 hb1]
    simp only [abs_mul, abs_neg, abs_pow,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hb0, abs_of_nonneg hi]
    change 2 * b ^ 2 * c * _ = _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [kernelQ, hden]
    ring
  let f : ℝ → ℝ := fun t => (1 - t) * kernelQ t c
  have hcont : Continuous f := by
    exact (continuous_const.sub continuous_id).mul (kernelQ_continuous hc.1)
  have hcontLeft : Continuous (fun t : ℝ => b * (1 - t) * kernelQ (b * t) c) := by
    exact (continuous_const.mul (continuous_const.sub continuous_id)).mul
      ((kernelQ_continuous hc.1).comp (continuous_const.mul continuous_id))
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      b * (1 - t) * kernelQ (b * t) c ≤ b * f (b * t) := by
    dsimp [f]
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (kernelQ_nonneg (mul_nonneg hb0 ht.1) hc.1)
    have h := mul_nonneg ht.1 (sub_nonneg.mpr hb1.le)
    nlinarith
  have hchange : (∫ t in (0 : ℝ)..1, b * f (b * t)) = ∫ t in (0 : ℝ)..b, f t := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left f hb]
    simp [smul_eq_mul, hb]
  calc
    |boundaryKernel b θ| = ∫ t in (0 : ℝ)..1, b * (1 - t) * kernelQ (b * t) c := hrep
    _ ≤ ∫ t in (0 : ℝ)..1, b * f (b * t) :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hcontLeft.intervalIntegrable _ _)
        ((continuous_const.mul (hcont.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
        hpoint
    _ = ∫ t in (0 : ℝ)..b, f t := hchange
    _ ≤ ∫ t in (0 : ℝ)..1, f t :=
      intervalIntegral.integral_mono_interval le_rfl hb0 hb1.le
        ((ae_restrict_iff' measurableSet_Ioc).mpr (.of_forall (fun t ht =>
          mul_nonneg (sub_nonneg.mpr ht.2) (kernelQ_nonneg ht.1.le hc.1))))
        (hcont.intervalIntegrable _ _)
    _ ≤ 3067 / 8100 := kernelQ_integral_bound hc

private theorem kernel_size_closed (b θ : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    |boundaryKernel b θ| ≤ 3067 / 8100 := by
  have hc : ContinuousOn (fun b => |boundaryKernel b θ|) (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.abs
    exact continuousOn_tsum (fun j => by unfold boundaryTerm; fun_prop)
      majorant_summable (fun j b hb => term_norm_le hb θ j)
  have hcl : closure (Ico (0 : ℝ) 1) = Icc (0 : ℝ) 1 := closure_Ico (by norm_num)
  exact le_on_closure (s := Ico (0 : ℝ) 1)
    (f := fun c => |boundaryKernel c θ|) (g := fun _ => 3067 / 8100)
    (fun c hc => kernel_size_interior c θ hc.1 hc.2)
    (by simpa only [hcl] using hc) continuousOn_const (by simpa only [hcl] using hb)

private theorem divided_cauchy_average (h : ℂ → ℂ) (hh : Differentiable ℂ h)
    (w : ℂ) (hw : ‖w‖ < 1) (hw0 : w ≠ 0) :
    Real.circleAverage (fun z => h z / (z - w)) 0 1 = (h w - h 0) / w := by
  have hden (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|) : z - w ≠ 0 := by
    intro he
    have hz' : ‖z‖ = 1 := by simpa using hz
    have he' := sub_eq_zero.mp he
    rw [he'] at hz'
    exact (ne_of_lt hw) hz'
  have hd : ContinuousOn (fun z => h z / (z - w)) (Metric.sphere (0 : ℂ) |(1 : ℝ)|) :=
    hh.continuous.continuousOn.div (continuousOn_id.sub continuousOn_const) hden
  have hwball : w ∈ Metric.ball (0 : ℂ) |(1 : ℝ)| := by simpa using hw
  have hdc : DiffContOnCl ℂ h (Metric.ball (0 : ℂ) |(1 : ℝ)|) := hh.diffContOnCl
  have hC := hdc.circleAverage_smul_div hwball
  have hC' : Real.circleAverage (fun z => (z / (z - w)) * h z) 0 1 = h w := by
    simpa only [sub_zero, smul_eq_mul] using hC
  have hmean : Real.circleAverage h 0 1 = h 0 := hdc.circleAverage
  have hpoint : Set.EqOn (fun z => (z / (z - w)) * h z)
      (fun z => h z + w * (h z / (z - w))) (Metric.sphere (0 : ℂ) |(1 : ℝ)|) := by
    intro z hz
    field_simp [hden z hz]
    <;> ring
  have hadd := Real.circleAverage_fun_add (f₁ := h)
    (f₂ := fun z => w * (h z / (z - w)))
    hh.continuous.continuousOn.circleIntegrable'
    ((show ContinuousOn (fun _ : ℂ => w) (Metric.sphere (0 : ℂ) |(1 : ℝ)|) from
      continuousOn_const).mul hd).circleIntegrable'
  have hsmul : Real.circleAverage (fun z => w * (h z / (z - w))) 0 1 =
      w * Real.circleAverage (fun z => h z / (z - w)) 0 1 := by
    simpa only [smul_eq_mul] using Real.circleAverage_fun_smul
      (a := w) (f := fun z => h z / (z - w)) (c := 0) (R := 1)
  have he := Real.circleAverage_congr_sphere hpoint
  rw [hC', hadd, hsmul, hmean] at he
  apply (eq_div_iff hw0).mpr
  linear_combination -he

private def rationalKernel (r : ℝ) (z : ℂ) : ℂ :=
  z / (1 + (r : ℂ) ^ 2 * z ^ 2)

private theorem rationalKernel_den_ne {r : ℝ} (hr : |r| < 1) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    1 + (r : ℂ) ^ 2 * z ^ 2 ≠ 0 := by
  have hr2 : |r| ^ 2 < 1 := by nlinarith [abs_nonneg r]
  have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hq : ‖(r : ℂ) ^ 2 * z ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [sq_nonneg |r|, sq_nonneg ‖z‖]
  intro he
  have he' : (r : ℂ) ^ 2 * z ^ 2 = -1 := by linear_combination he
  rw [he', norm_neg, norm_one] at hq
  exact lt_irrefl 1 hq

private theorem rational_zero_mean (h : ℂ → ℂ) (hh : Differentiable ℂ h)
    (r : ℝ) (hr : |r| < 1) :
    Real.circleAverage (fun z => rationalKernel r z * h z) 0 1 = 0 := by
  let F : ℂ → ℂ := fun z => rationalKernel r z * h z
  have hF : DiffContOnCl ℂ F (Metric.ball (0 : ℂ) |(1 : ℝ)|) := by
    constructor
    · intro z hz
      have hz' : ‖z‖ ≤ 1 := by
        exact (show ‖z‖ < 1 by simpa using hz).le
      apply DifferentiableAt.differentiableWithinAt
      dsimp [F, rationalKernel]
      exact ((differentiableAt_id.div
        ((differentiableAt_const _).add
          ((differentiableAt_const _).mul (differentiableAt_id.pow 2)))
        (rationalKernel_den_ne hr z hz')).mul (hh z))
    · rw [abs_one, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
      dsimp [F, rationalKernel]
      exact (continuousOn_id.div
        (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.pow 2)))
        (fun z hz => rationalKernel_den_ne hr z (by simpa using hz))).mul
        hh.continuous.continuousOn
  simpa [F, rationalKernel] using hF.circleAverage

/-- Uniform convergence, continuity, reflection, and the sign of the actual source kernel,
including the entire closed parameter edge `b = 1`. -/
theorem boundary_kernel_control (b θ : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    Continuous (boundaryKernel b) ∧
    boundaryKernel b (Real.pi - θ) = -boundaryKernel b θ ∧
    Real.cos θ * boundaryKernel b θ ≤ 0 ∧
    TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => ∑ j ∈ Finset.range n, boundaryTerm p.1 p.2 j)
      (fun p => boundaryKernel p.1 p.2) atTop {p | p.1 ∈ Icc (0 : ℝ) 1} ∧
    ContinuousOn (fun p : ℝ × ℝ => boundaryKernel p.1 p.2)
      {p | p.1 ∈ Icc (0 : ℝ) 1} ∧
    (∫ φ in (0 : ℝ)..(2 * Real.pi), boundaryKernel b φ) = 0 ∧
    |boundaryKernel b θ| ≤ 3067 / 8100 ∧ (3067 / 8100 : ℝ) < 19 / 50 := by
  refine ⟨kernel_continuous hb, kernel_reflection b θ, ?_, kernel_uniform_convergence,
    ?_, kernel_mean_zero hb, kernel_size_closed b θ hb, by norm_num⟩
  · have hc : ContinuousOn (fun b => Real.cos θ * boundaryKernel b θ) (Icc (0 : ℝ) 1) := by
      apply ContinuousOn.const_mul
      exact continuousOn_tsum (fun j => by unfold boundaryTerm; fun_prop)
        majorant_summable (fun j b hb => term_norm_le hb θ j)
    have hcl : closure (Ico (0 : ℝ) 1) = Icc (0 : ℝ) 1 := closure_Ico (by norm_num)
    exact le_on_closure (s := Ico (0 : ℝ) 1)
      (f := fun c => Real.cos θ * boundaryKernel c θ) (g := fun _ => 0)
      (fun c hc => kernel_sign_interior c θ hc.1 hc.2)
      (by simpa only [hcl] using hc) continuousOn_const (by simpa only [hcl] using hb)
  · exact continuousOn_tsum (fun j => by unfold boundaryTerm; fun_prop)
      majorant_summable (fun j p hp => term_norm_le hp p.2 j)

#print axioms boundary_kernel_control

end D5.S3.Analytic.Interpolation.SchurBoundaryKernel
