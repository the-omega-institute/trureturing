/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The complete Mangoldt remainder has an absolutely convergent arithmetic Laplace transform throughout the half-plane Re(s)>1. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (U)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane

private theorem ramp_norm_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => ∫ y : ℝ in Ioi 0,
      ‖Complex.exp (-s * y) * (mangoldtRamp n (Real.exp y) : ℂ)‖) := by
  let σ : ℂ := s.re
  have hσ : 1 < σ.re := hs
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt hσ).hasSum.div_const
      (σ * (σ - 1))
  apply (Complex.hasSum_re hsum).summable.congr
  intro n
  rw [← mangoldtRamp_laplace hσ]
  change RCLike.re (∫ y : ℝ in Ioi 0, Complex.exp (-σ * y) *
    (mangoldtRamp n (Real.exp y) : ℂ)) = _
  rw [← integral_re (mangoldtRamp_laplace_integrable (n := n) hσ)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  have he : Complex.exp (-σ * (y : ℂ)) = (Real.exp (-s.re * y) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  change (Complex.exp (-σ * (y : ℂ)) * (mangoldtRamp n (Real.exp y) : ℂ)).re = _
  simp only [he, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (mangoldtRamp_nonneg n _)]

private theorem weighted_ramps_hasSum (s : ℂ) (y : ℝ) :
    HasSum (fun n : ℕ => Complex.exp (-s * y) *
      (mangoldtRamp n (Real.exp y) : ℂ))
      (Complex.exp (-s * y) * (mangoldtPart (Real.exp y) : ℂ)) := by
  exact (Complex.hasSum_ofReal.mpr
    (mangoldtPart_summable (Real.exp_nonneg y)).hasSum).mul_left _

/-- Tonelli is paid at the norm level, before the complex integral is exchanged.
The positive ENNReal sum is finite by the actual Mangoldt LSeries at the real part of s. -/
private theorem part_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) *
      (mangoldtPart (Real.exp y) : ℂ)) (Ioi 0) := by
  let f : ℕ → ℝ → ℂ := fun n y => Complex.exp (-s * y) *
    (mangoldtRamp n (Real.exp y) : ℂ)
  let g : ℝ → ℂ := fun y => Complex.exp (-s * y) *
    (mangoldtPart (Real.exp y) : ℂ)
  have hi : ∀ n, Integrable (f n) (volume.restrict (Ioi 0)) := fun n =>
    mangoldtRamp_laplace_integrable hs
  have hm : AEStronglyMeasurable g (volume.restrict (Ioi 0)) := by
    have hp : Continuous (fun y : ℝ => mangoldtPart (Real.exp y)) := by
      have he : (fun y : ℝ => mangoldtPart (Real.exp y)) =
          (fun y : ℝ => U (Real.exp y) + Real.exp y * y -
            (1 + Real.eulerMascheroniConstant) * Real.exp y) := by
        funext y
        have h := U_eq_complete_ramps (Real.exp_nonneg y)
        rw [Real.log_exp] at h
        linarith only [h]
      rw [he]
      exact (U_exp_continuous.add (by fun_prop)).sub (by fun_prop)
    exact (show Continuous g by dsimp only [g]; fun_prop).aestronglyMeasurable
  refine ⟨hm, (hasFiniteIntegral_iff_norm g).mpr ?_⟩
  calc
    (∫⁻ y : ℝ, ENNReal.ofReal ‖g y‖ ∂volume.restrict (Ioi 0)) ≤
        ∫⁻ y : ℝ, ∑' n : ℕ, ENNReal.ofReal ‖f n y‖ ∂volume.restrict (Ioi 0) := by
      apply lintegral_mono
      intro y
      have hh : HasSum (fun n => f n y) (g y) := weighted_ramps_hasSum s y
      change ENNReal.ofReal ‖g y‖ ≤ ∑' n : ℕ, ENNReal.ofReal ‖f n y‖
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg (f n y)) hh.summable.norm]
      exact ENNReal.ofReal_le_ofReal (by
        rw [← hh.tsum_eq]
        exact norm_tsum_le_tsum_norm hh.summable.norm)
    _ = ∑' n : ℕ, ENNReal.ofReal
        (∫ y : ℝ in Ioi 0, ‖f n y‖) := by
      rw [lintegral_tsum (fun n => (hi n).aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal)]
      congr 1
      funext n
      simpa only [ofReal_norm] using
        (ofReal_integral_norm_eq_lintegral_enorm (hi n)).symm
    _ < ⊤ := (ramp_norm_summable hs).tsum_ofReal_lt_top

/-- Absolute summation, now exchanged with the complex Laplace integral. -/
private theorem part_laplace {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) *
      (mangoldtPart (Real.exp y) : ℂ)) =
        (-deriv riemannZeta s / riemannZeta s) /
          (s * (s - 1)) := by
  let f : ℕ → ℝ → ℂ := fun n y => Complex.exp (-s * y) *
    (mangoldtRamp n (Real.exp y) : ℂ)
  have hi : ∀ n, Integrable (f n) (volume.restrict (Ioi 0)) := fun n =>
    mangoldtRamp_laplace_integrable hs
  have hx := hasSum_integral_of_summable_integral_norm hi
    (ramp_norm_summable hs)
  have hx' : HasSum
      (fun n : ℕ => LSeries.term
        (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s n /
          (s * (s - 1)))
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) *
        (mangoldtPart (Real.exp y) : ℂ)) := by
    convert hx using 1
    · funext n
      exact (mangoldtRamp_laplace hs).symm
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      exact (weighted_ramps_hasSum s y).tsum_eq.symm
  have hL := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    hs).hasSum.div_const
      (s * (s - 1))
  change HasSum _ (LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
    s / (s * (s - 1))) at hL
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    hs] at hL
  exact hx'.unique hL

private theorem first_moment_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) *
      Complex.exp ((1 - s) * y)) (Ioi 0) := by
  have hr : IntegrableOn (fun y : ℝ => y * Real.exp (-(s.re - 1) * y)) (Ioi 0) := by
    simpa only [Real.rpow_one, one_mul, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (1 : ℝ)) (p := (1 : ℝ)) (b := s.re - 1)
        (by norm_num) (by norm_num) (sub_pos.mpr hs))
  refine hr.mono' (by
    exact (show Continuous (fun y : ℝ => (y : ℂ) *
      Complex.exp ((1 - s) * y)) by fun_prop).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact le_of_eq (by
    simp [Complex.norm_exp, Complex.mul_re, abs_of_nonneg (show 0 < y from hy).le])

/-- The first moment exists since the real exponential rate is strictly negative. -/
private theorem first_moment {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, (y : ℂ) * Complex.exp ((1 - s) * y)) =
      1 / (s - 1) ^ 2 := by
  let a : ℂ := 1 - s
  have ha : a.re = -(s.re - 1) := by simp [a]
  have ha0 : a ≠ 0 := by intro e; rw [e, Complex.zero_re] at ha; linarith
  let p : ℝ → ℂ := fun y => Complex.exp (a * y) * ((y : ℂ) / a - 1 / a ^ 2)
  have hd (y : ℝ) : HasDerivAt p ((y : ℂ) * Complex.exp (a * y)) y := by
    have he := ((hasDerivAt_id y).ofReal_comp.const_mul a).cexp
    have hl := ((hasDerivAt_id y).ofReal_comp.div_const a).sub_const (1 / a ^ 2)
    convert he.mul hl using 1
    · rfl
    · simp only [id_eq, Complex.ofReal_one]
      field_simp [ha0]
      ring
  have hlim : Tendsto p atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb : ∀ᶠ y : ℝ in atTop, ‖p y‖ ≤
        (y * Real.exp (-(s.re - 1) * y)) / ‖a‖ + Real.exp (-(s.re - 1) * y) / ‖a‖ ^ 2 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
      calc
        ‖p y‖ ≤ Real.exp (-(s.re - 1) * y) * (‖(y : ℂ) / a‖ + ‖1 / a ^ 2‖) := by
          dsimp only [p]
          rw [norm_mul, Complex.norm_exp]
          have har : (a * (y : ℂ)).re = -(s.re - 1) * y := by simp [Complex.mul_re, ha]
          rw [har]
          exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_nonneg _)
        _ = _ := by simp [norm_pow, abs_of_nonneg hy]; ring
    have hl : Tendsto (fun y : ℝ =>
        (y * Real.exp (-(s.re - 1) * y)) / ‖a‖ + Real.exp (-(s.re - 1) * y) / ‖a‖ ^ 2) atTop (𝓝 0) := by
      simpa only [Real.rpow_one, Real.rpow_zero, one_mul, zero_div, add_zero] using
        ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (s.re - 1) (sub_pos.mpr hs)).div_const ‖a‖).add
          ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (s.re - 1) (sub_pos.mpr hs)).div_const (‖a‖ ^ 2))
    exact squeeze_zero' (Eventually.of_forall (fun y => norm_nonneg (p y))) hb hl
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y _ => hd y) (first_moment_integrable hs) hlim
  simpa only [p, Complex.ofReal_zero, mul_zero, Complex.exp_zero, zero_div, zero_sub, one_mul,
    neg_neg, a, show 1 - s = -(s - 1) by ring,
    neg_sq] using h

private theorem U_weighted_split (s : ℂ) (y : ℝ) :
    Complex.exp (-s * y) * (U (Real.exp y) : ℂ) =
      Complex.exp (-s * y) * (mangoldtPart (Real.exp y) : ℂ) -
        (y : ℂ) * Complex.exp ((1 - s) * y) +
          ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) * Complex.exp ((1 - s) * y) := by
  rw [U_eq_complete_ramps (Real.exp_nonneg y), Real.log_exp]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_exp]
  have he : Complex.exp (-s * y) * Complex.exp (y : ℂ) =
      Complex.exp ((1 - s) * y) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = Complex.exp (-s * y) * (mangoldtPart (Real.exp y) : ℂ) -
        (y : ℂ) * (Complex.exp (-s * y) * Complex.exp (y : ℂ)) +
          ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
            (Complex.exp (-s * y) * Complex.exp (y : ℂ)) := by push_cast; ring
    _ = _ := by rw [he]; push_cast; rfl

private theorem complete_integrable {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) *
      (U (Real.exp y) : ℂ)) (Ioi 0) := by
  have hi := (part_integrable hs).sub (first_moment_integrable hs)
  have he := (integrableOn_exp_mul_complex_Ioi
    (by simpa using sub_neg.mpr hs : (1 - s).re < 0) 0).const_mul
      ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ)
  exact (hi.add he).congr (Eventually.of_forall fun y => (U_weighted_split _ y).symm)

/-- Integrating the complete ramp decomposition at a complex exponent. -/
private theorem complete_transform {s : ℂ} (hs : 1 < s.re) :
    (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) *
      (U (Real.exp y) : ℂ)) =
      (-deriv riemannZeta s / riemannZeta s) /
        (s * (s - 1)) -
          1 / (s - 1) ^ 2 +
            ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) / (s - 1) := by
  simp_rw [U_weighted_split]
  have hconst : IntegrableOn (fun y : ℝ =>
      ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
        Complex.exp ((1 - s) * y)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi
      (by simpa using sub_neg.mpr hs : (1 - s).re < 0) 0).const_mul _
  rw [integral_add (μ := volume.restrict (Ioi (0 : ℝ))) (f := fun y : ℝ =>
      Complex.exp (-s * y) * (mangoldtPart (Real.exp y) : ℂ) -
        (y : ℂ) * Complex.exp ((1 - s) * y))
    (g := fun y : ℝ => ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) *
      Complex.exp ((1 - s) * y))
    ((part_integrable hs).sub (first_moment_integrable hs))
    hconst,
    integral_sub (f := fun y : ℝ => Complex.exp (-s * y) *
      (mangoldtPart (Real.exp y) : ℂ))
      (g := fun y : ℝ => (y : ℂ) * Complex.exp ((1 - s) * y))
      (part_integrable hs) (first_moment_integrable hs),
    part_laplace hs, first_moment hs, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simpa using sub_neg.mpr hs : (1 - s).re < 0)]
  rw [show 1 - s = -(s - 1) by ring]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_neg]
  ring

/-- The exponentially damped complete Mangoldt remainder is absolutely integrable,
and its Laplace transform equals the corrected logarithmic derivative of zeta. -/
theorem u_laplace_half_plane {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => Complex.exp (-s * y) * (U (Real.exp y) : ℂ)) (Ioi 0) ∧
      (∫ y : ℝ in Ioi 0, Complex.exp (-s * y) * (U (Real.exp y) : ℂ)) =
        (-deriv riemannZeta s / riemannZeta s) / (s * (s - 1)) -
          1 / (s - 1) ^ 2 + ((1 + Real.eulerMascheroniConstant : ℝ) : ℂ) / (s - 1) :=
  ⟨complete_integrable hs, complete_transform hs⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtHalfPlane
end
