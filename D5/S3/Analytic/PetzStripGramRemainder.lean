/- GID: D5/S3/Analytic/PetzStripGramRemainder
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzStripGramRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact exponential deficit Gram dominates the logistic Gram of its boundary jump. -/

import D5.S3.Analytic.PetzLogisticEvaluation
import D5.S3.Analytic.PetzLogisticMidline

/-!
# Exponential deficit Gram on the Petz strip

The scalar Gram formula is the one used in §2 of
*Ordinary Petz recovery with an exactly pure retained qubit*.
The strip comparison uses the boundary weights of Yang,
*Quantum data processing equality*, arXiv:2609.33815v2, §III.1.
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ComplexOrder MatrixOrder

namespace PetzStripGramRemainder

open PetzLogisticMidline (line closedStrip lowerWeight upperWeight)
open PetzCothStripMode (lowerMode integral_lowerMode)
open PetzStripFiniteSeries (finiteOverlap overlapDeficit hasDerivAt_finiteOverlap_zero
  integral_finiteOverlap_strip)

noncomputable section

/-- The logistic Fourier transform, with its continuous value at zero. -/
def logistic (x : ℝ) : ℝ := if x = 0 then 1 else (x / 2) / Real.sinh (x / 2)

private def cothFactor (x : ℝ) : ℝ :=
  if x = 0 then 1 else (x / 2) * (Real.cosh (x / 2) / Real.sinh (x / 2))

/-- The scalar mode whose lower and upper boundary values enter the strip energy. -/
def deficit (x : ℝ) (z : ℂ) : ℂ := 1 - Complex.exp ((x : ℂ) * z)

/-- The closed form of the weighted strip Gram entry for the two deficit modes. -/
def stripGram (x y : ℝ) : ℝ :=
  -(x + y) / 2 + Real.exp (x / 2) * Real.exp (y / 2) * logistic (y - x) -
    cothFactor (y - x)

/-- A weighted conjugate product on the vertical line with real part `a`. -/
def weightedPair (w : ℝ → ℝ) (a x y t : ℝ) : ℂ :=
  (w t : ℂ) * (star (deficit x (line a t)) * deficit y (line a t))

private def verticalExponential (a x t : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * line a t)

local notation "mode" => verticalExponential 0

private theorem cross_vertical (a x y t : ℝ) :
    star (verticalExponential a x t) * verticalExponential a y t =
      (Real.exp ((x + y) * a) : ℂ) * mode (y - x) t := by
  unfold verticalExponential
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  simp only [line, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_zero,
    zero_add]
  push_cast
  ring

private theorem mode_re (x t : ℝ) : (mode x t).re = Real.cos (x * t) := by
  simp [verticalExponential, Complex.exp_re, Complex.mul_re, Complex.mul_im]

private theorem deficit_line (a x t : ℝ) :
    deficit x (line a t) = 1 - (Real.exp (x * a) : ℂ) * mode x t := by
  have h := cross_vertical a 0 x t
  simpa [deficit, verticalExponential] using congrArg (fun z : ℂ => 1 - z) h

private theorem weightedPair_expand (w : ℝ → ℝ) (a x y t : ℝ) :
    weightedPair w a x y t =
      (w t : ℂ) * (1 - (Real.exp (x * a) : ℂ) * mode (-x) t -
        (Real.exp (y * a) : ℂ) * mode y t +
        (Real.exp (x * a) : ℂ) * (Real.exp (y * a) : ℂ) * mode (y - x) t) := by
  have hx : star (mode x t) = mode (-x) t := by
    simpa [verticalExponential] using cross_vertical 0 x 0 t
  simp only [weightedPair, deficit_line, star_sub, star_one, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  rw [← Complex.star_def, hx]
  have hxy : mode (-x) t * mode y t = mode (y - x) t := by
    rw [← hx]
    simpa only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using
      cross_vertical 0 x y t
  rw [show (1 - mode (-x) t * (Real.exp (x * a) : ℂ)) *
        (1 - (Real.exp (y * a) : ℂ) * mode y t) =
      1 - (Real.exp (x * a) : ℂ) * mode (-x) t - (Real.exp (y * a) : ℂ) * mode y t +
        (Real.exp (x * a) : ℂ) * (Real.exp (y * a) : ℂ) * (mode (-x) t * mode y t)
    by ring, hxy]

private theorem mode_add_reflect (x t : ℝ) :
    mode x t + mode x (-t) = (2 : ℂ) * (Real.cos (x * t) : ℂ) := by
  have h (r : ℝ) : mode x r =
      Complex.cos ((x * r : ℝ) : ℂ) + Complex.I * Complex.sin ((x * r : ℝ) : ℂ) := by
    have harg : (x : ℂ) * line 0 r = ((x * r : ℝ) : ℂ) * Complex.I := by
      simp [line, mul_assoc, Complex.ofReal_mul]
    rw [verticalExponential, harg, Complex.exp_mul_I]
    ring
  rw [h t, h (-t)]
  simp only [mul_neg, Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos]
  ring

private theorem lower_diagonal (x t : ℝ) :
    lowerWeight t * ‖deficit x (line 0 t)‖ ^ 2 = 2 * lowerMode x t := by
  have h := weightedPair_expand lowerWeight 0 x x t
  have hn : (mode (-x) t).re = Real.cos (x * t) := by
    rw [mode_re, neg_mul, Real.cos_neg]
  have hleft : (weightedPair lowerWeight 0 x x t).re =
      lowerWeight t * ‖deficit x (line 0 t)‖ ^ 2 := by
    rw [weightedPair, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hzero : mode (x - x) t = 1 := by simp [verticalExponential]
  rw [← hleft]
  simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul, hzero] at h
  have hreal := congrArg Complex.re h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, Complex.sub_re, Complex.one_re, hn, mode_re] at hreal
  rw [hreal]
  change lowerWeight t * (1 - Real.cos (x * t) - Real.cos (x * t) + 1) =
    2 * (lowerWeight t * (1 - Real.cos (x * t)))
  ring

private theorem integrable_lower_pair (x y : ℝ) :
    Integrable (weightedPair lowerWeight 0 x y) := by
  have hm : Measurable lowerWeight := by
    unfold lowerWeight
    exact measurable_const.div (show Continuous
      (fun t : ℝ => Real.cosh (2 * Real.pi * t) - 1) by fun_prop).measurable
  have hd (r : ℝ) : Continuous (fun t => deficit r (line 0 t)) := by
    unfold deficit line
    fun_prop
  refine ((integral_lowerMode x).1.add (integral_lowerMode y).1).mono'
    ((Complex.continuous_ofReal.measurable.comp hm).mul
      ((continuous_star.comp (hd x)).measurable.mul (hd y).measurable)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hw : 0 ≤ lowerWeight t :=
    div_nonneg Real.pi_pos.le (sub_nonneg.mpr (Real.one_le_cosh _))
  have h := mul_le_mul_of_nonneg_left
    (show ‖deficit x (line 0 t)‖ * ‖deficit y (line 0 t)‖ ≤
      (‖deficit x (line 0 t)‖ ^ 2 + ‖deficit y (line 0 t)‖ ^ 2) / 2 by
      nlinarith [sq_nonneg (‖deficit x (line 0 t)‖ - ‖deficit y (line 0 t)‖)]) hw
  rw [← mul_div_assoc, mul_add, lower_diagonal, lower_diagonal] at h
  simp only [weightedPair, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hw,
    Pi.add_apply]
  linarith only [h]

private theorem integral_lower_pair (x y : ℝ) :
    (∫ t, weightedPair lowerWeight 0 x y t) =
      ((cothFactor x + cothFactor y - cothFactor (y - x) - 1 : ℝ) : ℂ) := by
  let f := weightedPair lowerWeight 0 x y
  let g (t : ℝ) := lowerMode x t + lowerMode y t - lowerMode (y - x) t
  have hf : Integrable f := integrable_lower_pair x y
  have hn : Integrable (fun t => f (-t)) := by
    simpa only [neg_one_mul] using hf.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)
  have hneg : (∫ t, f (-t)) = ∫ t, f t := by
    simpa only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using
      Measure.integral_comp_mul_left f (-1)
  have havg (t : ℝ) : f t + f (-t) = 2 * (g t : ℂ) := by
    have hw : lowerWeight (-t) = lowerWeight t := by
      simp [lowerWeight, mul_neg, Real.cosh_neg]
    simp only [f, weightedPair_expand, mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul, hw]
    rw [← mul_add]
    have he (v : ℝ) := mode_add_reflect v t
    simp only [g, lowerMode, ← show lowerWeight = PetzCothStripMode.lowerWeight from rfl]
    simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
    rw [show (1 - mode (-x) t - mode y t + mode (y - x) t) +
        (1 - mode (-x) (-t) - mode y (-t) + mode (y - x) (-t)) =
        2 - (mode (-x) t + mode (-x) (-t)) - (mode y t + mode y (-t)) +
          (mode (y - x) t + mode (y - x) (-t)) by ring, he, he, he]
    rw [neg_mul, Real.cos_neg]
    ring
  have h := congrArg (fun k : ℝ → ℂ => ∫ t, k t) (funext havg)
  change (∫ t, f t + f (-t)) = ∫ t, (2 : ℂ) * (g t : ℂ) at h
  have hcast : (∫ t, (g t : ℂ)) = Complex.ofReal (∫ t, g t) :=
    integral_ofReal (𝕜 := ℂ) (μ := volume) (f := g)
  rw [integral_add hf hn, hneg, integral_const_mul, hcast] at h
  have hm (r : ℝ) : (∫ t, lowerMode r t) = cothFactor r - 1 := by
    rw [(integral_lowerMode r).2]
    by_cases hr : r = 0 <;> simp [cothFactor, hr]
  have hg : (∫ t, g t) = cothFactor x + cothFactor y - cothFactor (y - x) - 1 := by
    have hxy : Integrable (fun t => lowerMode x t + lowerMode y t) :=
      (integral_lowerMode x).1.add (integral_lowerMode y).1
    change (∫ t, lowerMode x t + lowerMode y t - lowerMode (y - x) t) = _
    rw [integral_sub hxy (integral_lowerMode (y - x)).1,
      integral_add (integral_lowerMode x).1 (integral_lowerMode y).1, hm, hm, hm]
    ring
  rw [hg] at h
  change (∫ t, f t) = _
  linear_combination (1 / 2 : ℂ) * h

private theorem logistic_neg (x : ℝ) : logistic (-x) = logistic x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [logistic, hx, Real.sinh_neg, neg_div, div_neg]

private theorem integrable_weighted_mode (x : ℝ) :
    Integrable (fun t => (upperWeight t : ℂ) * mode x t) := by
  have hw : Continuous upperWeight := by
    unfold upperWeight
    exact continuous_const.div (by fun_prop)
      (fun t => ne_of_gt (by positivity [Real.cosh_pos (2 * Real.pi * t)]))
  have hm : Continuous (fun t => (upperWeight t : ℂ) * mode x t) :=
    (Complex.continuous_ofReal.comp hw).mul (by unfold verticalExponential line; fun_prop)
  apply (integrable_norm_iff hm.aestronglyMeasurable).1
  have hmNorm (t : ℝ) : ‖mode x t‖ = 1 := by
    rw [verticalExponential, Complex.norm_exp, Complex.mul_re, PetzLogisticMidline.line_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  simpa only [norm_mul, Complex.norm_real, hmNorm, mul_one]
    using PetzLogisticMidline.integrable_upperWeight.norm

/-- The factorization supplies the vanishing imaginary part and fixes the mass at zero. -/
private theorem upper_mode_real (x : ℝ) :
    ∃ r : ℝ, (∫ t, (upperWeight t : ℂ) * mode x t) = (r : ℂ) := by
  let ω : Bool → ℝ := fun b => if b then x else 0
  have h := (PetzLogisticEvaluation.exact_gram_factorization ω).2.2 false true
  refine ⟨‖PetzLogisticEvaluation.correlation ω false true‖ ^ 2, ?_⟩
  push_cast
  simpa only [ω, Bool.false_eq_true, ite_false, ite_true, sub_zero, verticalExponential,
    PetzLogisticMidline.line, Complex.ofReal_zero, zero_add, mul_assoc, Complex.ofReal_mul,
    show upperWeight = PetzExponentialBoundaryEvaluation.petzWeight from rfl] using h

private theorem upper_mass : (∫ t, upperWeight t) = 1 := by
  let ω : Unit → ℝ := fun _ => 0
  obtain ⟨_, hdiag, hentry⟩ := PetzLogisticEvaluation.exact_gram_factorization ω
  have h := hentry () ()
  rw [hdiag] at h
  have hcast : (∫ t, (upperWeight t : ℂ)) = Complex.ofReal (∫ t, upperWeight t) :=
    integral_ofReal (𝕜 := ℂ) (μ := volume) (f := upperWeight)
  have hc : (∫ t, (upperWeight t : ℂ)) = (1 : ℂ) := by
    simpa [ω, ← show upperWeight = PetzExponentialBoundaryEvaluation.petzWeight from rfl] using h
  rw [hcast] at hc
  exact_mod_cast hc

private theorem upper_mode_integral (x : ℝ) :
    (∫ t, (upperWeight t : ℂ) * mode x t) = (logistic x : ℂ) := by
  obtain ⟨r, hr⟩ := upper_mode_real x
  have hcos : (∫ t, upperWeight t * Real.cos (x * t)) = r := by
    have h := Complex.reCLM.integral_comp_comm (integrable_weighted_mode x)
    rw [hr] at h
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, mode_re] using h
  have hcosInt : Integrable (fun t => upperWeight t * Real.cos (x * t)) := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, mode_re] using
      Complex.reCLM.integrable_comp (integrable_weighted_mode x)
  let ω : Unit → ℝ := fun _ => x
  let c : Unit → ℂ := fun _ => 1
  have hdef (a t : ℝ) : overlapDeficit ω c a t =
      2 * (1 - Real.exp (x * a) * Real.cos (x * t)) := by
    unfold overlapDeficit finiteOverlap
    change 2 * (1 - (∑ i : Unit, c i * Complex.exp ((ω i : ℂ) * line a t)).re) = _
    simp [ω, c, Complex.exp_re, Complex.mul_re, Complex.mul_im]
  have hnonneg (t : ℝ) : 0 ≤ overlapDeficit ω c 0 t := by
    rw [hdef, mul_zero, Real.exp_zero, one_mul]
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.cos_le_one _))
  have hstrip := (integral_finiteOverlap_strip ω c (by simp [finiteOverlap, ω, c]) hnonneg).2.2
  rw [(hasDerivAt_finiteOverlap_zero ω c).deriv] at hstrip
  simp only [hdef, ω, c, Fintype.sum_unique, one_mul, Complex.ofReal_re, mul_zero, Real.exp_zero,
    mul_one_div] at hstrip
  change (∫ t, lowerWeight t * (2 * (1 - Real.cos (x * t)))) +
    (∫ t, upperWeight t * (2 * (1 - Real.exp (x / 2) * Real.cos (x * t)))) =
      -x at hstrip
  have hL (t : ℝ) : lowerWeight t * (2 * (1 - Real.cos (x * t))) = 2 * lowerMode x t := by
    change _ = 2 * (lowerWeight t * (1 - Real.cos (x * t)))
    ring
  have hU (t : ℝ) :
      upperWeight t * (2 * (1 - Real.exp (x / 2) * Real.cos (x * t))) =
        2 * (upperWeight t - Real.exp (x / 2) * (upperWeight t * Real.cos (x * t))) := by
    ring
  simp_rw [hL, hU] at hstrip
  rw [integral_const_mul, integral_const_mul,
    integral_sub PetzLogisticMidline.integrable_upperWeight (hcosInt.const_mul _),
    integral_const_mul, upper_mass, hcos, (integral_lowerMode x).2] at hstrip
  have he : Real.exp (x / 2) * r = Real.exp (x / 2) * logistic x := by
    by_cases hx : x = 0
    · subst x
      norm_num [logistic] at hstrip ⊢
      linarith
    have hs := Real.sinh_ne_zero.mpr (div_ne_zero hx (by norm_num : (2 : ℝ) ≠ 0))
    rw [ite_eq_right hx] at hstrip
    have hhyper : (x / 2) * (Real.cosh (x / 2) / Real.sinh (x / 2)) -
        Real.exp (x / 2) * logistic x = -x / 2 := by
      simp only [logistic, ite_eq_right hx, ← Real.cosh_add_sinh]
      field_simp [hs]
      ring
    linarith only [hstrip, hhyper]
  rw [hr, mul_left_cancel₀ (Real.exp_pos _).ne' he]

private theorem upper_pair (x y : ℝ) :
    Integrable (weightedPair upperWeight (1 / 2) x y) ∧
    (∫ t, weightedPair upperWeight (1 / 2) x y t) =
      ((1 - Real.exp (x / 2) * logistic x - Real.exp (y / 2) * logistic y +
        Real.exp (x / 2) * Real.exp (y / 2) * logistic (y - x) : ℝ) : ℂ) := by
  let a : ℂ := (Real.exp (x / 2) : ℂ)
  let b : ℂ := (Real.exp (y / 2) : ℂ)
  let f (r t : ℝ) := (upperWeight t : ℂ) * mode r t
  have hf (r : ℝ) : Integrable (f r) := integrable_weighted_mode r
  have hfun : weightedPair upperWeight (1 / 2) x y =
      fun t => f 0 t - a * f (-x) t - b * f y t + (a * b) * f (y - x) t := by
    funext t
    rw [weightedPair_expand]
    simp only [a, b, f, mul_one_div, verticalExponential, zero_mul, Complex.ofReal_zero,
      Complex.exp_zero, mul_one]
    ring
  rw [hfun]
  have hsub : Integrable (fun t => f 0 t - a * f (-x) t) :=
    (hf 0).sub ((hf (-x)).const_mul a)
  have hsub' : Integrable (fun t => f 0 t - a * f (-x) t - b * f y t) :=
    hsub.sub ((hf y).const_mul b)
  refine ⟨hsub'.add ((hf (y - x)).const_mul (a * b)), ?_⟩
  dsimp only
  rw [integral_add hsub' ((hf (y - x)).const_mul (a * b)),
    integral_sub hsub ((hf y).const_mul b), integral_sub (hf 0) ((hf (-x)).const_mul a)]
  simp only [integral_const_mul, f, upper_mode_integral, logistic_neg, a, b,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    show logistic 0 = 1 by simp [logistic]]

private theorem coth_sub_exp_logistic (x : ℝ) :
    cothFactor x - Real.exp (x / 2) * logistic x = -x / 2 := by
  by_cases hx : x = 0
  · simp [hx, cothFactor, logistic]
  have hs := Real.sinh_ne_zero.mpr (div_ne_zero hx (by norm_num : (2 : ℝ) ≠ 0))
  simp only [cothFactor, logistic, ite_eq_right hx, ← Real.cosh_add_sinh]
  field_simp [hs]
  ring

/-- Evaluate both boundary contributions to the Gram entry. Zero and coincident
frequencies use the same formula as the other entries. -/
theorem weighted_strip_gram (x y : ℝ) :
    Integrable (weightedPair lowerWeight 0 x y) ∧
    Integrable (weightedPair upperWeight (1 / 2) x y) ∧
    (∫ t, weightedPair lowerWeight 0 x y t) +
      (∫ t, weightedPair upperWeight (1 / 2) x y t) = (stripGram x y : ℂ) := by
  refine ⟨integrable_lower_pair x y, (upper_pair x y).1, ?_⟩
  rw [integral_lower_pair, (upper_pair x y).2, ← Complex.ofReal_add]
  congr 1
  unfold stripGram
  linarith only [coth_sub_exp_logistic x, coth_sub_exp_logistic y]

private theorem quadratic_norm {ι : Type*} [Fintype ι]
    (c v : ι → ℂ) (w : ℝ) :
    (∑ i, ∑ j, (star (c i) * c j) * ((w : ℂ) * (star (v i) * v j))) =
      ((w * ‖∑ i, c i * v i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.star_def, star_sum, star_mul]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem energy_integral {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (v : ι → ℝ → ℂ) (w : ℝ → ℝ)
    (hi : ∀ i j, Integrable (fun t => (w t : ℂ) * (star (v i t) * v j t))) :
    Integrable (fun t => w t * ‖∑ i, c i * v i t‖ ^ 2) ∧
      ((∫ t, w t * ‖∑ i, c i * v i t‖ ^ 2 : ℝ) : ℂ) =
        ∑ i, ∑ j, (star (c i) * c j) * ∫ t, (w t : ℂ) * (star (v i t) * v j t) := by
  let f (i j : ι) (t : ℝ) := (star (c i) * c j) * ((w t : ℂ) * (star (v i t) * v j t))
  have hf (i j : ι) : Integrable (f i j) := (hi i j).const_mul _
  have hpoint (t : ℝ) := quadratic_norm c (fun i => v i t) (w t)
  have hiSum : Integrable (fun t => ∑ i, ∑ j, f i j t) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf i j))
  have hiCast : Integrable (fun t => ((w t * ‖∑ i, c i * v i t‖ ^ 2 : ℝ) : ℂ)) :=
    hiSum.congr (Filter.Eventually.of_forall hpoint)
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re]
      using Complex.reCLM.integrable_comp hiCast
  · let g (t : ℝ) := w t * ‖∑ i, c i * v i t‖ ^ 2
    have hcast : (∫ t, (g t : ℂ)) = Complex.ofReal (∫ t, g t) :=
      integral_ofReal (𝕜 := ℂ) (μ := volume) (f := g)
    change Complex.ofReal (∫ t, g t) = _
    rw [← hcast]
    dsimp only [g]
    simp_rw [← hpoint]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hf i j)]
    simp only [f, integral_const_mul]

private theorem logistic_gram_entry (x y : ℝ) :
    Integrable (fun t => (upperWeight t : ℂ) * (star (mode x t) * mode y t)) ∧
    (∫ t, (upperWeight t : ℂ) * (star (mode x t) * mode y t)) =
      (logistic (y - x) : ℂ) := by
  have h (t : ℝ) : star (mode x t) * mode y t = mode (y - x) t := by
    simpa only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using
      cross_vertical 0 x y t
  simp_rw [h]
  exact ⟨integrable_weighted_mode _, upper_mode_integral _⟩

private theorem boundary_jump (x t : ℝ) :
    deficit x (line (1 / 2) t) - deficit x (line 0 t) =
      (1 - (Real.exp (x / 2) : ℂ)) * mode x t := by
  simp only [deficit_line, mul_one_div, mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
  ring

/-- The closed remainder Gram after subtracting the logistic energy of the jump. -/
def remainder (x y : ℝ) : ℝ :=
  stripGram x y - (1 - Real.exp (x / 2)) * (1 - Real.exp (y / 2)) * logistic (y - x)

/-- The exact closed remainder is nonnegative on arbitrary finite complex amplitudes.
The frequencies may coincide or vanish. -/
theorem remainder_quadratic_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) (c : ι → ℂ) :
    0 ≤ (∑ i, ∑ j, (star (c i) * c j) * (remainder (x i) (x j) : ℂ)).re := by
  let F (z : ℂ) := ∑ i, c i * deficit (x i) z
  let u (i : ι) : ℂ := c i * (1 - (Real.exp (x i / 2) : ℂ))
  have hd : Differentiable ℂ F := by unfold F deficit; fun_prop
  have hb (z : ℂ) (hz : z ∈ closedStrip) :
      ‖F z‖ ≤ ∑ i, ‖c i‖ * (1 + Real.exp (|x i| / 2)) := by
    have hz' : 0 ≤ z.re ∧ z.re ≤ 1 / 2 := hz
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact add_le_add_right (Real.exp_le_exp.mpr (calc
      x i * z.re ≤ |x i| * z.re :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hz'.1
      _ ≤ |x i| / 2 := by
        rw [← mul_one_div]
        exact mul_le_mul_of_nonneg_left hz'.2 (abs_nonneg _))) _
  have hL := energy_integral c (fun i t => deficit (x i) (line 0 t)) lowerWeight
    (fun i j => (weighted_strip_gram (x i) (x j)).1)
  have hU := energy_integral c (fun i t => deficit (x i) (line (1 / 2) t)) upperWeight
    (fun i j => (weighted_strip_gram (x i) (x j)).2.1)
  have hJ := energy_integral u (fun i t => mode (x i) t) upperWeight
    (fun i j => (logistic_gram_entry (x i) (x j)).1)
  have hjump (t : ℝ) : F (line (1 / 2) t) - F (line 0 t) = ∑ i, u i * mode (x i) t := by
    dsimp only [F]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [u]
    rw [← mul_sub, boundary_jump, mul_assoc]
  have hstrip := (PetzLogisticMidline.full_logistic_strip
    hd.continuous.continuousOn hd.differentiableOn hb hL.1).2.2
  simp_rw [hjump] at hstrip
  have hsum : ((∫ t, lowerWeight t * ‖F (line 0 t)‖ ^ 2 : ℝ) : ℂ) +
      ((∫ t, upperWeight t * ‖F (line (1 / 2) t)‖ ^ 2 : ℝ) : ℂ) -
      ((∫ t, upperWeight t * ‖∑ i, u i * mode (x i) t‖ ^ 2 : ℝ) : ℂ) =
        ∑ i, ∑ j, (star (c i) * c j) * (remainder (x i) (x j) : ℂ) := by
    dsimp only [F]
    rw [hL.2, hU.2, hJ.2, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_add]
    change _ * ((∫ t, weightedPair lowerWeight 0 (x i) (x j) t) +
      ∫ t, weightedPair upperWeight (1 / 2) (x i) (x j) t) -
      _ * (∫ t, (upperWeight t : ℂ) * (star (mode (x i) t) * mode (x j) t)) = _
    rw [(weighted_strip_gram (x i) (x j)).2.2, (logistic_gram_entry (x i) (x j)).2]
    simp only [u, star_mul, star_sub, star_one, Complex.star_def, Complex.conj_ofReal, remainder]
    push_cast
    ring
  have hreal := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at hreal
  linarith only [hstrip, hreal]

#print axioms weighted_strip_gram
#print axioms remainder_quadratic_nonneg

end

end PetzStripGramRemainder
