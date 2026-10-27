/- GID: D5/S3/Weil/ZetaExplicit/ExponentialStripSampling
   generality: I
   mirror-B: none(waiver:noncompact-exponential-reproduction)
   mirror-E: none(waiver:infinite-complex-zero-sampling)
   anchors: []
   utility: none
   digest: Noncompact exponential reproduction supplies uniform closed-strip zero sampling. -/

import D5.S3.Weil.ZetaExplicit.WeightedZeroSampling
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic

/-!
Candidate mathematical content fixed before compilation: the tilted damping
exp(-a|x|-beta*x), a>1/2, has its literal complex Cauchy Fourier kernel.
The positive real part of its denominator pays a uniform inverse-square
bound on the entire closed half-strip. Existing noncompact Fubini,
Cauchy--Schwarz and actual zero counting are reused, not re-proved.
The sampling consumer retains the logarithmic energy of the
exponentially weighted input; original H6 alone does not supply that premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Zeta23.WeilEF.ExponentialStripSampling

open Real Complex Set MeasureTheory Filter
open scoped Topology ComplexConjugate FourierTransform

open private convolution_inversion convolution_norm_sq_le
  weighted_zero_sampling_two_families from
  D5.S3.Weil.ZetaExplicit.WeightedZeroSampling

private def damping (a beta x : ℝ) : ℂ :=
  Complex.exp ((-a * |x| - beta * x : ℝ) : ℂ)

private def cauchyKernel (a : ℝ) (z : ℂ) : ℂ :=
  ((a / Real.pi : ℝ) : ℂ) / ((a : ℂ) ^ 2 + z ^ 2)

private def margin (a : ℝ) : ℝ := min 1 (a ^ 2 - 1 / 4)

private def envelope (a : ℝ) : ℝ := a / (Real.pi * margin a)

private theorem margin_pos {a : ℝ} (ha : 1 / 2 < a) : 0 < margin a := by
  apply lt_min (by norm_num)
  nlinarith

private theorem denominator_bound {a : ℝ}
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    margin a * (1 + z.re ^ 2) ≤ ‖(a : ℂ) ^ 2 + z ^ 2‖ := by
  have hm1 : margin a ≤ 1 := min_le_left _ _
  have hmd : margin a ≤ a ^ 2 - 1 / 4 := min_le_right _ _
  have hzsq : z.im ^ 2 ≤ 1 / 4 := by
    obtain ⟨hl, hu⟩ := abs_le.mp hz
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hm1 (sq_nonneg z.re)
  have hre : ((a : ℂ) ^ 2 + z ^ 2).re = a ^ 2 + z.re ^ 2 - z.im ^ 2 := by
    simp only [pow_two, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hreal : margin a * (1 + z.re ^ 2) ≤ ((a : ℂ) ^ 2 + z ^ 2).re := by
    rw [hre]
    nlinarith only [hmd, hzsq, hmul]
  exact hreal.trans (Complex.re_le_norm _)

private theorem cauchyKernel_bound {a : ℝ} (ha : 1 / 2 < a)
    {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖cauchyKernel a z‖ ≤ envelope a / (1 + z.re ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hm := margin_pos ha
  have hd := denominator_bound (a := a) hz
  rw [cauchyKernel, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos ha0 Real.pi_pos)]
  calc
    _ ≤ (a / Real.pi) / (margin a * (1 + z.re ^ 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = envelope a / (1 + z.re ^ 2) := by
      dsimp only [envelope]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem tilted_exp_fourier {a beta : ℝ} (ha : 1 / 2 < a)
    (hb : |beta| ≤ 1 / 2) (t : ℝ) :
    Integrable (fun x : ℝ => damping a beta x *
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) ∧
    Zeta23.paperFT (damping a beta) t =
      (2 * (a : ℂ)) / ((a : ℂ) ^ 2 + ((t : ℂ) + Complex.I * (beta : ℂ)) ^ 2) := by
  let cp : ℂ := ((-a - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let cm : ℂ := ((a - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  have hpr : cp.re < 0 := by
    dsimp only [cp]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
    linarith [(abs_le.mp hb).1]
  have hmr : 0 < cm.re := by
    dsimp only [cm]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
    linarith [(abs_le.mp hb).2]
  have hiP := integrableOn_exp_mul_complex_Ioi hpr 0
  have hiM := integrableOn_exp_mul_complex_Iic hmr 0
  let f : ℝ → ℂ := fun x => damping a beta x *
    Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
  have eP : EqOn f (fun x : ℝ => Complex.exp (cp * (x : ℂ))) (Ioi 0) := by
    intro x hx
    dsimp only [f, damping]
    rw [← Complex.exp_add, abs_of_pos hx]
    congr 1
    dsimp only [cp]
    push_cast
    ring
  have eM : EqOn f (fun x : ℝ => Complex.exp (cm * (x : ℂ))) (Iic 0) := by
    intro x hx
    dsimp only [f, damping]
    rw [← Complex.exp_add, abs_of_nonpos hx]
    congr 1
    dsimp only [cm]
    push_cast
    ring
  have hfiP := hiP.congr_fun eP.symm measurableSet_Ioi
  have hfiM := hiM.congr_fun eM.symm measurableSet_Iic
  have hfi : Integrable f := by
    have h := hfiM.union hfiP
    simpa only [Iic_union_Ioi, integrableOn_univ] using h
  refine ⟨hfi, ?_⟩
  change (∫ x : ℝ, f x) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi hfiM hfiP,
    setIntegral_congr_fun measurableSet_Iic eM,
    setIntegral_congr_fun measurableSet_Ioi eP,
    integral_exp_mul_complex_Iic hmr 0, integral_exp_mul_complex_Ioi hpr 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hcp : cp ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.zero_re] at he
    linarith
  have hcm : cm ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.zero_re] at he
    linarith
  have hd : (a : ℂ) ^ 2 + ((t : ℂ) + Complex.I * (beta : ℂ)) ^ 2 ≠ 0 := by
    intro h
    have hp := denominator_bound (a := a) (z := ((t : ℂ) + Complex.I * (beta : ℂ)))
      (by simpa using hb)
    rw [h, norm_zero] at hp
    have hm := margin_pos ha
    have hx : 0 < margin a * (1 + (((t : ℂ) + Complex.I * (beta : ℂ)).re) ^ 2) :=
      mul_pos hm (by positivity)
    linarith
  field_simp [hcp, hcm, hd]
  dsimp only [cp, cm]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem integrable_cauchyKernel {a beta : ℝ} (ha : 1 / 2 < a)
    (hb : |beta| ≤ 1 / 2) :
    Integrable (fun t : ℝ =>
      cauchyKernel a ((t : ℂ) + Complex.I * (beta : ℂ))) := by
  have hz (t : ℝ) :
      |((t : ℂ) + Complex.I * (beta : ℂ)).im| ≤ 1 / 2 := by
    simpa using hb
  have hden (t : ℝ) :
      (a : ℂ) ^ 2 + ((t : ℂ) + Complex.I * (beta : ℂ)) ^ 2 ≠ 0 := by
    have hbound := denominator_bound (a := a) (hz t)
    have hpositive : 0 < margin a *
        (1 + ((t : ℂ) + Complex.I * (beta : ℂ)).re ^ 2) :=
      mul_pos (margin_pos ha) (by positivity)
    exact norm_pos_iff.mp (hpositive.trans_le hbound)
  have hc : Continuous (fun t : ℝ =>
      cauchyKernel a ((t : ℂ) + Complex.I * (beta : ℂ))) := by
    unfold cauchyKernel
    exact continuous_const.div (by fun_prop) hden
  apply (integrable_inv_one_add_sq.const_mul (envelope a)).mono'
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    simpa [div_eq_mul_inv] using cauchyKernel_bound ha (hz t)

private theorem tilted_kernel_inversion {a beta : ℝ} (ha : 1 / 2 < a)
    (hb : |beta| ≤ 1 / 2) (x : ℝ) :
    (∫ t : ℝ, cauchyKernel a ((t : ℂ) + Complex.I * (beta : ℂ)) *
      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) =
        damping a beta x := by
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hscale : (2 * Real.pi : ℂ) * ((a / Real.pi : ℝ) : ℂ) =
      2 * (a : ℂ) := by
    push_cast
    field_simp [hpi]
    <;> ring
  have hpair (t : ℝ) : Zeta23.paperFT (damping a beta) t =
      (2 * Real.pi : ℂ) *
        cauchyKernel a ((t : ℂ) + Complex.I * (beta : ℂ)) := by
    rw [(tilted_exp_fourier ha hb t).2, cauchyKernel,
      ← mul_div_assoc, hscale]
  have hpaper : Integrable
      (fun t : ℝ => Zeta23.paperFT (damping a beta) t) := by
    apply ((integrable_cauchyKernel ha hb).const_mul (2 * Real.pi : ℂ)).congr
    exact Filter.Eventually.of_forall fun t => (hpair t).symm
  have hfourier : Integrable (𝓕 (damping a beta)) := by
    have hc := hpaper.comp_mul_left' (R := -(2 * Real.pi))
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero))
    apply hc.congr
    filter_upwards with w
    rw [Zeta23.EF.paperFT_ofReal_eq_fourier]
    congr 1
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hdamp : Integrable (damping a beta) := by
    simpa only [Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, mul_one] using (tilted_exp_fourier ha hb 0).1
  have hcont : Continuous (damping a beta) := by
    unfold damping
    fun_prop
  have hinv := Zeta23.EF.paper_inversion hcont hdamp hfourier x
  have hcancel : (1 / (2 * Real.pi) : ℂ) * (2 * Real.pi : ℂ) = 1 := by
    field_simp [hpi]
  have hscaled (t : ℝ) :
      (1 / (2 * Real.pi) : ℂ) * Zeta23.paperFT (damping a beta) t =
        cauchyKernel a ((t : ℂ) + Complex.I * (beta : ℂ)) := by
    rw [hpair t, ← mul_assoc, hcancel, one_mul]
  calc
    (∫ t : ℝ, cauchyKernel a ((t : ℂ) + Complex.I * (beta : ℂ)) *
        Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))) =
        ∫ t : ℝ,
          ((1 / (2 * Real.pi) : ℂ) * Zeta23.paperFT (damping a beta) t) *
            Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        dsimp only
        rw [hscaled t]
    _ = (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ, Zeta23.paperFT (damping a beta) t *
          Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ)) := by
      rw [← Zeta23.EF.cintegral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => mul_assoc _ _ _
    _ = damping a beta x := hinv.symm

private theorem damped_convolution_reproduction {a beta : ℝ}
    (ha : 1 / 2 < a) (hb : |beta| ≤ 1 / 2)
    {h : ℝ → ℂ} (hh : Integrable h) (t : ℝ) :
    (∫ s : ℝ, cauchyKernel a (((t - s : ℝ) : ℂ) + Complex.I * (beta : ℂ)) *
      Zeta23.paperFT h s) =
      Zeta23.paperFT (fun x : ℝ => damping a 0 x * h x)
        ((t : ℂ) + Complex.I * (beta : ℂ)) := by
  rw [convolution_inversion hh (integrable_cauchyKernel ha hb)
    (tilted_kernel_inversion ha hb)]
  unfold Zeta23.paperFT
  apply integral_congr_ae
  filter_upwards with x
  dsimp only [damping]
  calc
    _ = h x * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ) +
        ((-a * |x| - beta * x : ℝ) : ℂ)) := by
      rw [Complex.exp_add]
      ring
    _ = h x * Complex.exp (((-a * |x| - 0 * x : ℝ) : ℂ) +
        Complex.I * ((t : ℂ) + Complex.I * (beta : ℂ)) * (x : ℂ)) := by
      congr 2
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    _ = _ := by rw [Complex.exp_add]; ring

private theorem noncompact_strip_estimate {a : ℝ} (ha : 1 / 2 < a)
    {h : ℝ → ℂ} (hh : Integrable h)
    (hlog : Integrable (fun s : ℝ => Real.log (|s| + 3) *
      ‖Zeta23.paperFT h s‖ ^ 2))
    (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    ‖Zeta23.paperFT (fun x : ℝ => damping a 0 x * h x) z‖ ^ 2 ≤
      (Real.pi * envelope a ^ 2) *
        ∫ s : ℝ, ‖Zeta23.paperFT h s‖ ^ 2 / (1 + (z.re - s) ^ 2) := by
  let K : ℝ → ℂ := fun s =>
    cauchyKernel a (((z.re - s : ℝ) : ℂ) + Complex.I * (z.im : ℂ))
  let C : ℝ := envelope a
  have hC : 0 ≤ C := by
    dsimp only [C, envelope]
    exact le_of_lt (div_pos (by linarith) (mul_pos Real.pi_pos (margin_pos ha)))
  have hF : Continuous (fun s : ℝ => Zeta23.paperFT h s) := by
    simp only [Zeta23.paperFT_ofReal_eq_fourier]
    have hc := VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hh
    exact hc.comp (by fun_prop)
  have hweight (t : ℝ) : Integrable (fun s : ℝ =>
      ‖Zeta23.paperFT h s‖ ^ 2 / (1 + (t - s) ^ 2)) := by
    have hmeas : Continuous (fun s : ℝ =>
        ‖Zeta23.paperFT h s‖ ^ 2 / (1 + (t - s) ^ 2)) :=
      (hF.norm.pow 2).div (by fun_prop) (fun s => by positivity)
    apply hlog.mono' hmeas.aestronglyMeasurable
    filter_upwards with s
    rw [Real.norm_of_nonneg (by positivity)]
    have hL : 1 ≤ Real.log (|s| + 3) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith [Real.exp_one_lt_d9, abs_nonneg s]
    calc
      _ ≤ ‖Zeta23.paperFT h s‖ ^ 2 :=
        div_le_self (sq_nonneg _) (by nlinarith [sq_nonneg (t - s)])
      _ ≤ Real.log (|s| + 3) * ‖Zeta23.paperFT h s‖ ^ 2 := by
        nlinarith [sq_nonneg ‖Zeta23.paperFT h s‖]
  have hK : Integrable K :=
    (integrable_cauchyKernel ha hz).comp_sub_left z.re
  have hKb (s : ℝ) : ‖K s‖ ≤ C / (1 + (z.re - s) ^ 2) := by
    simpa only [K, C, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add, Complex.add_re, Complex.mul_re, mul_zero, sub_zero, add_zero] using
      cauchyKernel_bound ha (z := (((z.re - s : ℝ) : ℂ) + Complex.I * (z.im : ℂ)))
        (by simpa using hz)
  have hmajor : Integrable (fun s : ℝ => C / (1 + (z.re - s) ^ 2)) := by
    simpa only [div_eq_mul_inv] using
      (integrable_inv_one_add_sq.comp_sub_left z.re).const_mul C
  have hKF : Integrable (fun s : ℝ => ‖K s‖ * ‖Zeta23.paperFT h s‖ ^ 2) := by
    apply ((hweight z.re).const_mul C).mono'
      (hK.aestronglyMeasurable.norm.mul (hF.norm.pow 2).aestronglyMeasurable)
    filter_upwards with s
    change ‖‖K s‖ * ‖Zeta23.paperFT h s‖ ^ 2‖ ≤
      C * (‖Zeta23.paperFT h s‖ ^ 2 / (1 + (z.re - s) ^ 2))
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _))]
    calc
      _ ≤ (C / (1 + (z.re - s) ^ 2)) * ‖Zeta23.paperFT h s‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hKb s) (sq_nonneg _)
      _ = _ := by ring
  have hKint : (∫ s : ℝ, ‖K s‖) ≤ C * Real.pi := by
    calc
      _ ≤ ∫ s : ℝ, C / (1 + (z.re - s) ^ 2) :=
        integral_mono hK.norm hmajor hKb
      _ = C * Real.pi := by
        simp only [div_eq_mul_inv, integral_const_mul]
        rw [integral_sub_left_eq_self (fun s : ℝ => (1 + s ^ 2)⁻¹) volume z.re,
          integral_univ_inv_one_add_sq]
  have hKFint : (∫ s : ℝ, ‖K s‖ * ‖Zeta23.paperFT h s‖ ^ 2) ≤
      C * ∫ s : ℝ, ‖Zeta23.paperFT h s‖ ^ 2 / (1 + (z.re - s) ^ 2) := by
    rw [← integral_const_mul]
    apply integral_mono hKF ((hweight z.re).const_mul C)
    intro s
    calc
      _ ≤ (C / (1 + (z.re - s) ^ 2)) * ‖Zeta23.paperFT h s‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hKb s) (sq_nonneg _)
      _ = _ := by ring
  have hrepro := damped_convolution_reproduction ha hz hh z.re
  have hzeta : (z.re : ℂ) + Complex.I * (z.im : ℂ) = z := by
    apply Complex.ext <;> simp
  rw [hzeta] at hrepro
  rw [← hrepro]
  calc
    _ ≤ (∫ s : ℝ, ‖K s‖) * ∫ s : ℝ, ‖K s‖ * ‖Zeta23.paperFT h s‖ ^ 2 :=
      convolution_norm_sq_le hK hF.aestronglyMeasurable hKF
    _ ≤ (C * Real.pi) *
        (C * ∫ s : ℝ, ‖Zeta23.paperFT h s‖ ^ 2 / (1 + (z.re - s) ^ 2)) :=
      mul_le_mul hKint hKFint (integral_nonneg (fun s => by positivity)) (by positivity)
    _ = _ := by dsimp only [C]; ring

/-- Exponential damping, together with logarithmic Fourier energy of the
undamped L1 input, supplies both original multiplicity-weighted sampling
families on the entire closed strip. The constant is independent of support.
This does not infer the logarithmic energy premise from a physical moment. -/
theorem weighted_zero_sampling_exponential (a : ℝ) (ha : 1 / 2 < a) :
    ∃ C_a : ℝ, 0 ≤ C_a ∧ ∀ (Z : Zeta23.ZeroConfig) (A : ℝ), 1 ≤ A →
      (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) →
      ∀ h : ℝ → ℂ, Integrable h →
      Integrable (fun s : ℝ => Real.log (|s| + 3) *
        Complex.normSq (Zeta23.paperFT h s)) →
      (Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT
            (fun x : ℝ => Complex.exp ((-a * |x| : ℝ) : ℂ) * h x) (Zeta23.gammaOf ρ))) ∧
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Complex.normSq (Zeta23.paperFT
          (fun x : ℝ => Complex.exp ((-a * |x| : ℝ) : ℂ) * h x) (Zeta23.gammaOf ρ))) ≤
          C_a * A * Zeta23.WeilEF.totalWeight *
            ∫ s : ℝ, Real.log (|s| + 3) * Complex.normSq (Zeta23.paperFT h s)) ∧
      (Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) *
          Complex.normSq (Zeta23.paperFT
            (fun x : ℝ => Complex.exp ((-a * |x| : ℝ) : ℂ) * h x)
              (conj (Zeta23.gammaOf ρ)))) ∧
        (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) * Complex.normSq (Zeta23.paperFT
          (fun x : ℝ => Complex.exp ((-a * |x| : ℝ) : ℂ) * h x)
            (conj (Zeta23.gammaOf ρ)))) ≤
          C_a * A * Zeta23.WeilEF.totalWeight *
            ∫ s : ℝ, Real.log (|s| + 3) * Complex.normSq (Zeta23.paperFT h s)) := by
  let B : ℝ := Real.pi * envelope a ^ 2
  refine ⟨8 * B, by dsimp only [B]; positivity, ?_⟩
  intro Z A hA hlocal h hh hlog
  have hlog' : Integrable (fun s : ℝ => Real.log (|s| + 3) *
      ‖Zeta23.paperFT h s‖ ^ 2) := by
    simpa only [Complex.normSq_eq_norm_sq] using hlog
  have hF : Continuous (fun s : ℝ => Zeta23.paperFT h s) := by
    simp only [Zeta23.paperFT_ofReal_eq_fourier]
    have hc := VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hh
    exact hc.comp (by fun_prop)
  have hkernel (t : ℝ) : Integrable (fun s : ℝ =>
      ‖Zeta23.paperFT h s‖ ^ 2 / (1 + (t - s) ^ 2)) := by
    have hmeas : Continuous (fun s : ℝ =>
        ‖Zeta23.paperFT h s‖ ^ 2 / (1 + (t - s) ^ 2)) :=
      (hF.norm.pow 2).div (by fun_prop) (fun s => by positivity)
    apply hlog'.mono' hmeas.aestronglyMeasurable
    filter_upwards with s
    rw [Real.norm_of_nonneg (by positivity)]
    have hL : 1 ≤ Real.log (|s| + 3) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith [Real.exp_one_lt_d9, abs_nonneg s]
    calc
      _ ≤ ‖Zeta23.paperFT h s‖ ^ 2 :=
        div_le_self (sq_nonneg _) (by nlinarith [sq_nonneg (t - s)])
      _ ≤ Real.log (|s| + 3) * ‖Zeta23.paperFT h s‖ ^ 2 := by
        nlinarith [sq_nonneg ‖Zeta23.paperFT h s‖]
  have hstrip := noncompact_strip_estimate ha hh hlog'
  have hout := weighted_zero_sampling_two_families Z hA
    (show 0 ≤ B by dsimp only [B]; positivity) hlocal hlog'
    (Filter.Eventually.of_forall (fun s => sq_nonneg ‖Zeta23.paperFT h s‖)) hkernel hstrip
  simpa only [damping, zero_mul, sub_zero, Complex.normSq_eq_norm_sq, mul_assoc] using hout

#print axioms weighted_zero_sampling_exponential

end Zeta23.WeilEF.ExponentialStripSampling
