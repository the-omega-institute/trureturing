/- GID: D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean
   generality: G
   mirror-B: D5/B/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.MeasureTheory.Integral.Bochner.Set, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrability.Basic, mathlib/module/Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Slope]
   utility: none
   digest: Exact circle means and mixed-norm violations for holomorphic power families. -/

import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Defs
import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Radial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The holomorphic power family, its circle means, and normalized evaluations. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Defs
open D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Radial

namespace D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean

/-- Principal-branch powers of an affine function. -/
def powerFamily (p a : ℝ) : ℂ → ℂ :=
  fun w => Complex.exp ((2 / p : ℂ) * Complex.log (1 + a * w))

private lemma affine_mem_slitPlane {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {w : ℂ} (hw : ‖w‖ < 1) : 1 + (a : ℂ) * w ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  exact (mul_le_mul_of_nonneg_left hw.le ha).trans_lt (by simpa using ha1)

/-- The power family is holomorphic on the open unit disc. -/
theorem powerFamily_differentiableOn {p a : ℝ} (_hp : 0 < p)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    DifferentiableOn ℂ (powerFamily p a) (Metric.ball 0 1) := by
  intro w hw
  have hs := affine_mem_slitPlane ha ha1 (by simpa using hw)
  have hf : DifferentiableAt ℂ (fun v : ℂ => 1 + (a : ℂ) * v) w := by fun_prop
  exact (Complex.differentiableAt_exp.comp w
    (((Complex.differentiableAt_log hs).comp w hf).const_mul (2 / (p : ℂ)))).differentiableWithinAt

/-- The norm of the power family is the corresponding real power. -/
theorem norm_powerFamily {p a : ℝ} (_hp : 0 < p) (ha : 0 ≤ a) (ha1 : a < 1)
    {w : ℂ} (hw : ‖w‖ < 1) :
    ‖powerFamily p a w‖ = ‖1 + (a : ℂ) * w‖ ^ (2 / p) := by
  have hs := affine_mem_slitPlane ha ha1 hw
  have hn : 0 < ‖1 + (a : ℂ) * w‖ := norm_pos_iff.mpr (Complex.slitPlane_ne_zero hs)
  have hc : (2 / (p : ℂ)) = ((2 / p : ℝ) : ℂ) := by push_cast; rfl
  rw [powerFamily, hc, Complex.norm_exp, Complex.re_ofReal_mul, Complex.log_re,
    Real.rpow_def_of_pos hn, mul_comm]

private lemma powerFamily_bound {p a : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (ha1 : a < 1)
    {w : ℂ} (hw : ‖w‖ < 1) : ‖powerFamily p a w‖ ≤ (1 + a) ^ (2 / p) := by
  rw [norm_powerFamily hp ha ha1 hw]
  apply Real.rpow_le_rpow (norm_nonneg _) _ (by positivity)
  calc
    ‖1 + (a : ℂ) * w‖ ≤ ‖(1 : ℂ)‖ + ‖(a : ℂ) * w‖ := norm_add_le _ _
    _ ≤ 1 + a := by
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
      nlinarith [hw.le]

private lemma norm_circle {ρ θ : ℝ} (hρ : 0 ≤ ρ) :
    ‖(ρ : ℂ) * Complex.exp (θ * Complex.I)‖ = ρ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ,
    Complex.norm_exp_ofReal_mul_I, mul_one]

private lemma circle_square (a ρ θ : ℝ) :
    ‖1 + (a : ℂ) * ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ ^ 2 =
      1 + 2 * a * ρ * Real.cos θ + a ^ 2 * ρ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.exp_mul_I, Complex.mul_re, Complex.mul_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [congrArg (fun x : ℝ => a ^ 2 * ρ ^ 2 * x) (Real.sin_sq_add_cos_sq θ)]

private lemma circle_power {p a ρ : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (ha1 : a < 1)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (θ : ℝ) :
    ‖powerFamily p a ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ ^ p =
      1 + 2 * a * ρ * Real.cos θ + a ^ 2 * ρ ^ 2 := by
  rw [norm_powerFamily hp ha ha1 (by rw [norm_circle hρ]; exact hρ1),
    ← Real.rpow_mul (norm_nonneg _), div_mul_cancel₀ 2 hp.ne', Real.rpow_two,
    circle_square]

/-- The exact angular mean of the power family. -/
theorem circleMean_powerFamily {p a ρ : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (ha1 : a < 1)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    circleMean (ENNReal.ofReal p) (powerFamily p a) ρ =
      ENNReal.ofReal ((1 + a ^ 2 * ρ ^ 2) ^ (1 / p)) := by
  let F : ℝ → ℝ := fun θ => 1 + 2 * a * ρ * Real.cos θ + a ^ 2 * ρ ^ 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hFn (θ : ℝ) : 0 ≤ F θ := by
    rw [show F θ = ‖powerFamily p a ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ ^ p
      from (circle_power hp ha ha1 hρ hρ1 θ).symm]
    positivity
  have hFi : IntervalIntegrable F volume 0 (2 * Real.pi) := hF.intervalIntegrable _ _
  have hI : (∫ θ in (0 : ℝ)..2 * Real.pi, F θ) =
      (2 * Real.pi) * (1 + a ^ 2 * ρ ^ 2) := by
    dsimp [F]
    rw [intervalIntegral.integral_add
      ((intervalIntegrable_const).add (Real.continuous_cos.intervalIntegrable _ _ |>.const_mul _))
      intervalIntegrable_const,
      intervalIntegral.integral_add intervalIntegrable_const
        (Real.continuous_cos.intervalIntegrable _ _ |>.const_mul _),
      intervalIntegral.integral_const_mul, integral_cos]
    simp [Real.sin_two_pi]
    ring
  have hlin : (∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi),
      (‖powerFamily p a ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖₊ : ℝ≥0∞) ^ p) =
      ENNReal.ofReal ((2 * Real.pi) * (1 + a ^ 2 * ρ ^ 2)) := by
    have hh := ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hFi)
      (Filter.Eventually.of_forall hFn)
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le, hI] at hh
    rw [hh]
    apply lintegral_congr
    intro θ
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
      circle_power hp ha ha1 hρ hρ1]
  simp only [circleMean, ENNReal.ofReal_ne_top, ↓reduceIte,
    ENNReal.toReal_ofReal hp.le]
  rw [hlin, ← ENNReal.ofReal_div_of_pos Real.two_pi_pos,
    mul_div_cancel_left₀ _ Real.two_pi_pos.ne',
    ENNReal.ofReal_rpow_of_pos (by positivity)]

private lemma radial_integrable {p q α a : ℝ} (hα : 0 < α) (hq : 0 < q) :
    IntervalIntegrable (fun ρ : ℝ =>
      ρ * (1 - ρ ^ 2) ^ (α * q - 1) * (1 + a ^ 2 * ρ ^ 2) ^ (q / p)) volume 0 1 := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2) using 1
    · rfl
    · simp <;> ring
  have hi : IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) ^ (α * q - 1) * (-2 * x))
      volume 0 1 := by
    apply (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
      (f := fun x : ℝ => 1 - x ^ 2) (f' := fun x => -2 * x)
      (g := fun u => u ^ (α * q - 1)) (by fun_prop)
      (fun x _ => hd x) (by intro x hx; simp only [min_eq_left zero_le_one] at hx; nlinarith [hx.1])).mpr
    exact intervalIntegral.intervalIntegrable_rpow' (by nlinarith [mul_pos hα hq])
  have hw : IntervalIntegrable (fun x : ℝ => x * (1 - x ^ 2) ^ (α * q - 1)) volume 0 1 := by
    convert hi.const_mul (-1 / 2 : ℝ) using 1
    ext x
    ring
  have hc : Continuous (fun x : ℝ => (1 + a ^ 2 * x ^ 2) ^ (q / p)) := by
    apply Continuous.rpow_const (by fun_prop)
    intro x
    left
    positivity
  exact hw.mul_continuousOn hc.continuousOn

/-- Reduction of the finite mixed norm to its real radial integral. -/
theorem mixedNorm_powerFamily_finite {p q α a : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hα : 0 < α) (ha : 0 ≤ a) (ha1 : a < 1) :
    mixedNorm (ENNReal.ofReal p) (ENNReal.ofReal q) α (powerFamily p a) =
      ENNReal.ofReal ((radialIntegral p q α (a ^ 2)) ^ (1 / q)) := by
  let F : ℝ → ℝ := fun ρ =>
    ρ * (1 - ρ ^ 2) ^ (α * q - 1) * (1 + a ^ 2 * ρ ^ 2) ^ (q / p)
  have hFn : ∀ ρ ∈ Ioo (0 : ℝ) 1, 0 ≤ F ρ := by
    intro ρ hρ
    have hρ0 := hρ.1.le
    have : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
    dsimp [F]
    positivity
  have hFi : IntegrableOn F (Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (radial_integrable hα hq)
  have hlin : (∫⁻ ρ in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (ρ * (1 - ρ ^ 2) ^ (α * q - 1)) *
        circleMean (ENNReal.ofReal p) (powerFamily p a) ρ ^ q) =
      ENNReal.ofReal (∫ ρ in (0 : ℝ)..1, F ρ) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hFi
        ((ae_restrict_mem measurableSet_Ioo).mono fun ρ hρ => hFn ρ hρ)]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro ρ hρ
    dsimp only
    rw [circleMean_powerFamily hp ha ha1 hρ.1.le hρ.2,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (by positivity) _),
      ← Real.rpow_mul (by positivity), show (1 / p) * q = q / p by ring,
      ← ENNReal.ofReal_mul (by
        have hρ0 := hρ.1.le
        have : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
        positivity)]
  have hInt : 0 ≤ ∫ ρ in (0 : ℝ)..1, F ρ := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_nonneg measurableSet_Ioo hFn
  simp only [mixedNorm, ENNReal.ofReal_ne_top, ↓reduceIte, ENNReal.toReal_ofReal hq.le]
  rw [hlin, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity) hInt) (by positivity)]
  rfl

/-- Every finite-parameter power family has finite mixed norm. -/
theorem mixedNorm_powerFamily_lt_top {p q α a : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hα : 0 < α) (ha : 0 ≤ a) (ha1 : a < 1) :
    mixedNorm (ENNReal.ofReal p) (ENNReal.ofReal q) α (powerFamily p a) < ∞ := by
  rw [mixedNorm_powerFamily_finite hp hq hα ha ha1]
  exact ENNReal.ofReal_lt_top

private lemma evaluation_point {p α a : ℝ} (hp : 0 < p) (hα : 0 < α)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    0 ≤ 1 / (1 + α * p) * a ∧ 1 / (1 + α * p) * a < 1 := by
  have hc : 0 < 1 / (1 + α * p) := by positivity
  have hc1 : 1 / (1 + α * p) ≤ 1 :=
    (div_le_one (by positivity : 0 < 1 + α * p)).mpr (by nlinarith [mul_pos hα hp])
  exact ⟨mul_nonneg hc.le ha, (mul_le_mul_of_nonneg_right hc1 ha).trans_lt (by simpa using ha1)⟩

/-- Exact normalized evaluation at the distinguished real point. -/
theorem evaluation_powerFamily {p q α a : ℝ} (hp : 0 < p) (hα : 0 < α)
    (ha : 0 ≤ a) (ha1 : a < 1) :
    let c := 1 / (1 + α * p)
    ‖powerFamily p a ((c * a : ℝ) : ℂ)‖ ^ q *
      (1 - (c * a) ^ 2) ^ (q * (α + 1 / p)) = evaluationExcess p q α (a ^ 2) := by
  let c := 1 / (1 + α * p)
  have hpt := evaluation_point hp hα ha ha1
  have hz : ‖((c * a : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpt.1]
    exact hpt.2
  have hc : 0 < c := by dsimp [c]; positivity
  have he : (1 : ℂ) + (a : ℂ) * ((c * a : ℝ) : ℂ) = ((1 + c * a ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  dsimp only
  rw [norm_powerFamily hp ha ha1 hz, he, Complex.norm_of_nonneg (by positivity),
    ← Real.rpow_mul (by positivity)]
  dsimp [evaluationExcess, c] at *
  congr 2 <;> ring

/-- A strict radial gap gives a counterexample with all analytic side conditions. -/
theorem refutes_of_gap {p q α a : ℝ} (hp : 0 < p) (hq : 0 < q) (hα : 0 < α)
    (ha : 0 < a) (ha1 : a < 1)
    (hgap : radialIntegral p q α (a ^ 2) < evaluationExcess p q α (a ^ 2)) :
    let z : ℂ := ((1 / (1 + α * p) * a : ℝ) : ℂ)
    DifferentiableOn ℂ (powerFamily p a) (Metric.ball 0 1) ∧
    mixedNorm (ENNReal.ofReal p) (ENNReal.ofReal q) α (powerFamily p a) < ∞ ∧
    ‖z‖ < 1 ∧
    mixedNorm (ENNReal.ofReal p) (ENNReal.ofReal q) α (powerFamily p a) <
      ENNReal.ofReal ‖powerFamily p a z‖ *
        ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (α + 1 / (ENNReal.ofReal p).toReal)) ∧
    (∀ w : ℂ, ‖w‖ < 1 → ‖powerFamily p a w‖ ≤ (1 + a) ^ (2 / p)) := by
  let c := 1 / (1 + α * p)
  let z : ℂ := ((c * a : ℝ) : ℂ)
  have hpt := evaluation_point hp hα ha.le ha1
  have hzn : ‖z‖ = c * a := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpt.1]
  have hz : ‖z‖ < 1 := hzn.trans_lt hpt.2
  refine ⟨powerFamily_differentiableOn hp ha.le ha1,
    mixedNorm_powerFamily_lt_top hp hq hα ha.le ha1, hz, ?_⟩
  constructor
  · let U : ℝ := ‖powerFamily p a z‖ * (1 - ‖z‖ ^ 2) ^ (α + 1 / p)
    have hb : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have hU : 0 ≤ U := by dsimp [U]; positivity
    have hUq : U ^ q = evaluationExcess p q α (a ^ 2) := by
      rw [Real.mul_rpow (norm_nonneg _) (Real.rpow_nonneg hb.le _),
        ← Real.rpow_mul hb.le, mul_comm (α + 1 / p), hzn]
      exact evaluation_powerFamily hp hα ha.le ha1
    have hN : 0 ≤ radialIntegral p q α (a ^ 2) := by
      unfold radialIntegral
      apply mul_nonneg (by positivity)
      apply intervalIntegral.integral_nonneg zero_le_one
      intro ρ hρ
      have hρ0 := hρ.1
      have : 0 ≤ 1 - ρ ^ 2 := by nlinarith [hρ.1, hρ.2]
      positivity
    have hroot : (radialIntegral p q α (a ^ 2)) ^ (1 / q) < U := by
      by_contra hh
      have hle := Real.rpow_le_rpow hU (le_of_not_gt hh) hq.le
      rw [← Real.rpow_mul hN, one_div_mul_cancel hq.ne', Real.rpow_one, hUq] at hle
      exact (not_lt_of_ge hle) hgap
    rw [mixedNorm_powerFamily_finite hp hq hα ha.le ha1,
      ENNReal.toReal_ofReal hp.le, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.rpow_nonneg hN _)).mpr hroot
  · intro w hw
    exact powerFamily_bound hp ha.le ha1 hw

private lemma weighted_mean_le_one {p α t u : ℝ} (hp : 0 < p) (hα : 0 < α)
    (ht : 0 ≤ t) (htp : t ≤ α * p) (hu : 0 ≤ u) (hu1 : u < 1) :
    (1 - u) ^ α * (1 + t * u) ^ (1 / p) ≤ 1 := by
  have h1 : 0 < 1 - u := by linarith
  have h2 : 0 < 1 + t * u := by positivity
  rw [Real.rpow_def_of_pos h1, Real.rpow_def_of_pos h2, ← Real.exp_add,
    Real.exp_le_one_iff]
  have hlog1 := Real.log_le_sub_one_of_pos h1
  have hlog2 := Real.log_le_sub_one_of_pos h2
  have hpa : t / p ≤ α := (div_le_iff₀ hp).mpr htp
  have hmul := mul_le_mul_of_nonneg_right hpa hu
  have hA := mul_le_mul_of_nonneg_right hlog1 hα.le
  have hB := mul_le_mul_of_nonneg_right hlog2 (by positivity : 0 ≤ 1 / p)
  have heq : (1 + t * u - 1) * (1 / p) = t / p * u := by ring
  rw [heq] at hB
  linarith

/-- The infinity mixed norm is exactly one in the small-parameter range. -/
theorem mixedNorm_powerFamily_infinity {p α a : ℝ} (hp : 0 < p) (hα : 0 < α)
    (ha : 0 ≤ a) (ha1 : a < 1) (haα : a ^ 2 ≤ α * p) :
    mixedNorm (ENNReal.ofReal p) ∞ α (powerFamily p a) = 1 := by
  have heq : mixedNorm (ENNReal.ofReal p) ∞ α (powerFamily p a) =
      ⨆ ρ ∈ Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((1 - ρ ^ 2) ^ α * (1 + a ^ 2 * ρ ^ 2) ^ (1 / p)) := by
    simp only [mixedNorm, ↓reduceIte]
    apply iSup_congr
    intro ρ
    apply iSup_congr
    intro hρ
    rw [circleMean_powerFamily hp ha ha1 hρ.1.le hρ.2,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by nlinarith [hρ.1, hρ.2]) _)]
  rw [heq]
  apply le_antisymm
  · refine iSup₂_le fun ρ hρ => ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    exact weighted_mean_le_one hp hα (sq_nonneg a) haα (sq_nonneg ρ)
      (by nlinarith [hρ.1, hρ.2])
  · have hc : ContinuousAt (fun ρ : ℝ =>
        (1 - ρ ^ 2) ^ α * (1 + a ^ 2 * ρ ^ 2) ^ (1 / p)) 0 := by
      fun_prop (disch := norm_num)
    have hlim := (ENNReal.continuous_ofReal.continuousAt.comp hc).tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hbound : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
        ENNReal.ofReal ((1 - ρ ^ 2) ^ α * (1 + a ^ 2 * ρ ^ 2) ^ (1 / p)) ≤
          ⨆ ρ ∈ Ioo (0 : ℝ) 1,
            ENNReal.ofReal ((1 - ρ ^ 2) ^ α * (1 + a ^ 2 * ρ ^ 2) ^ (1 / p)) := by
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))] with ρ hρ hρ1
      exact le_iSup₂_of_le ρ ⟨hρ, hρ1⟩ le_rfl
    simpa using le_of_tendsto hlim hbound

private lemma infinity_evaluation_excess {p α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t ≤ α * p ∧
      let c := 1 / (1 + α * p)
      1 < (1 + c * t) ^ (2 / p) * (1 - c ^ 2 * t) ^ (α + 1 / p) := by
  let c := 1 / (1 + α * p)
  let E : ℝ → ℝ := fun t =>
    (1 + c * t) ^ (2 / p) * (1 - c ^ 2 * t) ^ (α + 1 / p)
  have hd1 := (((hasDerivAt_id (0 : ℝ)).const_mul c).const_add 1).rpow_const
    (p := 2 / p) (Or.inl (by simp))
  have hd2 := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul (c ^ 2))).rpow_const
      (p := α + 1 / p) (Or.inl (by simp))
  have hd : HasDerivAt E (1 / (p * (1 + α * p))) 0 := by
    convert hd1.mul hd2 using 1
    · rfl
    · simp only [id_eq, mul_zero, add_zero, Real.one_rpow, Pi.sub_apply, sub_zero,
        zero_sub, mul_one, one_mul]
      dsimp [c]
      field_simp
      <;> ring
  have hs := hd.tendsto_slope_zero_right.eventually
    (lt_mem_nhds (by positivity : 0 < 1 / (p * (1 + α * p))))
  have hm : 0 < min 1 (α * p) := lt_min zero_lt_one (mul_pos hα hp)
  have hright : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < min 1 (α * p) :=
    nhdsWithin_le_nhds (gt_mem_nhds hm)
  obtain ⟨t, ht⟩ := (hs.and (hright.and hsmall)).exists
  have ht0 : 0 < t := ht.2.1
  refine ⟨t, ht0, (lt_min_iff.mp ht.2.2).1, (lt_min_iff.mp ht.2.2).2.le, ?_⟩
  have hslope : 0 < (E t - 1) / t := by
    simpa [E, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht.1
  have : 0 < E t - 1 := (div_pos_iff_of_pos_right ht0).mp hslope
  change 1 < E t
  linarith

/-- For every finite positive p and every positive alpha the infinity case fails. -/
theorem refutes_at_infinity {p α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    ∃ a : ℝ, a ∈ Ioo (0 : ℝ) 1 ∧ ∃ z : ℂ, ‖z‖ < 1 ∧
      mixedNorm (ENNReal.ofReal p) ∞ α (powerFamily p a) < ∞ ∧
      mixedNorm (ENNReal.ofReal p) ∞ α (powerFamily p a) <
        ENNReal.ofReal ‖powerFamily p a z‖ *
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (α + 1 / (ENNReal.ofReal p).toReal)) ∧
      (∀ w : ℂ, ‖w‖ < 1 → ‖powerFamily p a w‖ ≤ (1 + a) ^ (2 / p)) := by
  obtain ⟨t, ht0, ht1, htα, hE⟩ := infinity_evaluation_excess hp hα
  let a := Real.sqrt t
  have ha : 0 < a := Real.sqrt_pos.mpr ht0
  have ha1 : a < 1 := (Real.sqrt_lt' zero_lt_one).mpr (by simpa using ht1)
  have hat : a ^ 2 = t := Real.sq_sqrt ht0.le
  let c := 1 / (1 + α * p)
  let z : ℂ := ((c * a : ℝ) : ℂ)
  have hpt := evaluation_point hp hα ha.le ha1
  have hzn : ‖z‖ = c * a := by
    dsimp [z]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpt.1]
  have hz : ‖z‖ < 1 := hzn.trans_lt hpt.2
  have he : (1 : ℂ) + (a : ℂ) * z = ((1 + c * t : ℝ) : ℂ) := by
    dsimp [z]
    rw [← hat]
    push_cast
    ring
  have hnorm := mixedNorm_powerFamily_infinity hp hα ha.le ha1 (hat ▸ htα)
  refine ⟨a, ⟨ha, ha1⟩, z, hz, hnorm ▸ ENNReal.one_lt_top, ?_⟩
  constructor
  · rw [hnorm, ENNReal.toReal_ofReal hp.le, ← ENNReal.ofReal_mul (norm_nonneg _)]
    rw [norm_powerFamily hp ha.le ha1 hz, he, Complex.norm_of_nonneg (by
      have : 0 < c := by dsimp [c]; positivity
      positivity), hzn, mul_pow, hat]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one).mpr hE
  · intro w hw
    exact powerFamily_bound hp ha.le ha1 hw

end D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.CircleMean
