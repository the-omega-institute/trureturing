/- GID: D5/S3/Weil/ZetaBridge/ExponentialPrimeCorrelationPassage
   generality: G
   mirror-B: none(waiver:integral-series-domination-limit)
   mirror-E: none(waiver:infinite-arithmetic-limit)
   anchors: []
   utility: none
   digest: One exponential envelope pays passage through the complete Weil prime correlation. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
The full original Weil correlation,
both signs of log n, every von Mangoldt coefficient and every prime power
are retained. A fixed exp(-|x|) envelope gives an exp(-3|s|/4) correlation
majorant, which puts the arithmetic series strictly inside Re(s)>1.
This is an arithmetic domain passage, not an explicit formula or positivity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage

open Real MeasureTheory Filter Set
open scoped Topology ComplexConjugate Convolution
open Zeta23.EF

private def majorant (x : ℝ) : ℝ := exp (-|x| / 4)

private theorem majorant_integrable : Integrable majorant := by
  have hi : Integrable (fun x : ℝ => exp (-|x| / 2)) := by
    simpa only [RCLike.re_eq_complex_re, Complex.ofReal_re] using
      integrable_exp_neg_abs_half.re
  have hs := hi.comp_mul_left' (by norm_num : (1 / 2 : ℝ) ≠ 0)
  convert hs using 1
  ext x
  simp only [majorant, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  congr 1
  ring

private theorem correlation_bound_pointwise {A : ℝ} (hA : 0 ≤ A)
    {f : ℝ → ℂ} (hf : ∀ x, ‖f x‖ ≤ A * exp (-|x|)) (s x : ℝ) :
    ‖f x * conj (f (x - s))‖ ≤
      (A ^ 2 * exp (-3 * |s| / 4)) * majorant x := by
  have htriangle : |s| ≤ |x| + |x - s| := by
    have h := abs_sub x (x - s)
    simpa only [sub_sub_cancel] using h
  rw [norm_mul, Complex.norm_conj]
  calc
    _ ≤ (A * exp (-|x|)) * (A * exp (-|x - s|)) :=
      mul_le_mul (hf x) (hf (x-s)) (norm_nonneg _) (by positivity)
    _ = A ^ 2 * exp (-|x| - |x - s|) := by
      rw [show -|x| - |x - s| = -|x| + -|x - s| by ring, exp_add]
      ring
    _ ≤ A ^ 2 * exp ((-3 * |s| / 4) + (-|x| / 4)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [abs_nonneg (x-s)]))
        (sq_nonneg A)
    _ = _ := by rw [exp_add]; dsimp [majorant]; ring

private def envelopeConstant (A : ℝ) : ℝ := A ^ 2 * ∫ x : ℝ, majorant x

private theorem correlation_bound {A : ℝ} (hA : 0 ≤ A)
    {f : ℝ → ℂ} (hc : Continuous f)
    (hf : ∀ x, ‖f x‖ ≤ A * exp (-|x|)) (s : ℝ) :
    Integrable (fun x : ℝ => f x * conj (f (x-s))) ∧
      ‖weilTest f f s‖ ≤ envelopeConstant A * exp (-3 * |s| / 4) := by
  have hm := majorant_integrable.const_mul (A ^ 2 * exp (-3 * |s| / 4))
  have hb : ∀ᵐ x : ℝ ∂volume, ‖f x * conj (f (x-s))‖ ≤
      (A ^ 2 * exp (-3 * |s| / 4)) * majorant x :=
    Eventually.of_forall (correlation_bound_pointwise hA hf s)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => f x * conj (f (x-s))) volume :=
    (hc.mul (Complex.continuous_conj.comp
      (hc.comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
  refine ⟨hm.mono' hmeas hb, ?_⟩
  simp only [weilTest, convolution_def, ContinuousLinearMap.mul_apply', tilde, neg_sub]
  calc
    _ ≤ ∫ x : ℝ, (A ^ 2 * exp (-3 * |s| / 4)) * majorant x :=
      norm_integral_le_of_norm_le hm hb
    _ = _ := by rw [integral_const_mul]; dsimp [envelopeConstant]; ring

private theorem correlation_tendsto {A : ℝ} (hA : 0 ≤ A)
    {f : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hc : ∀ k, Continuous (f k))
    (hf : ∀ k x, ‖f k x‖ ≤ A * exp (-|x|))
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (g x))) (s : ℝ) :
    Tendsto (fun k => weilTest (f k) (f k) s) atTop (𝓝 (weilTest g g s)) := by
  simp only [weilTest, convolution_def, ContinuousLinearMap.mul_apply', tilde, neg_sub]
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ => (A ^ 2 * exp (-3 * |s| / 4)) * majorant x)
  · intro k
    exact ((hc k).mul (Complex.continuous_conj.comp
      ((hc k).comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
  · exact majorant_integrable.const_mul _
  · intro k
    exact Eventually.of_forall (correlation_bound_pointwise hA (hf k) s)
  · exact Eventually.of_forall fun x =>
      (hlim x).mul ((Complex.continuous_conj.tendsto _).comp (hlim (x-s)))

private def primeTerm (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
    (weilTest f f (log n) + weilTest f f (-log n))

private def arithmeticEnvelope (n : ℕ) : ℝ :=
  ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (5/4 : ℂ) n‖

private theorem arithmeticEnvelope_summable : Summable arithmeticEnvelope :=
  summable_norm_iff.mpr
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num : 1 < (5/4 : ℂ).re))

private theorem primeTerm_bound {A : ℝ} (hA : 0 ≤ A)
    {f : ℝ → ℂ} (hc : Continuous f)
    (hf : ∀ x, ‖f x‖ ≤ A * exp (-|x|)) (n : ℕ) :
    ‖primeTerm f n‖ ≤ (2 * envelopeConstant A) * arithmeticEnvelope n := by
  by_cases hn : n = 0
  · subst n
    simp [primeTerm, arithmeticEnvelope, LSeries.term_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg hn1
  have hb := (correlation_bound hA hc hf (log n)).2
  have hb' := (correlation_bound hA hc hf (-log n)).2
  rw [abs_neg] at hb'
  rw [abs_of_nonneg hlog] at hb hb'
  have hcoef : 0 ≤ ArithmeticFunction.vonMangoldt n / sqrt n := by positivity
  have hexp : exp (-3 * log (n : ℝ) / 4) = (n : ℝ) ^ (-3/4 : ℝ) := by
    rw [rpow_def_of_pos hn0]
    congr 1
    ring
  have henv : arithmeticEnvelope n =
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (5 / 4 : ℝ) := by
    rw [arithmeticEnvelope, LSeries.norm_term_eq, if_neg hn]
    have hre : (5 / 4 : ℂ).re = (5 / 4 : ℝ) := by norm_num
    rw [hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hpower : (n : ℝ) ^ (-(1 / 2) : ℝ) * (n : ℝ) ^ (-3 / 4 : ℝ) =
      (n : ℝ) ^ (-(5 / 4) : ℝ) := by
    rw [← rpow_add hn0]
    congr 1
    ring
  have hscale : (ArithmeticFunction.vonMangoldt n / sqrt n) *
      exp (-3 * log (n : ℝ) / 4) = arithmeticEnvelope n := by
    rw [henv]
    calc
      _ = ArithmeticFunction.vonMangoldt n *
          ((n : ℝ) ^ (-(1 / 2) : ℝ) * (n : ℝ) ^ (-3 / 4 : ℝ)) := by
        rw [hexp, sqrt_eq_rpow, div_eq_mul_inv, ← rpow_neg hn0.le]
        ring
      _ = _ := by
        rw [hpower, rpow_neg hn0.le]
        exact (div_eq_mul_inv _ _).symm
  rw [primeTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef]
  calc
    _ ≤ (ArithmeticFunction.vonMangoldt n / sqrt n) *
        (2 * envelopeConstant A * exp (-3 * log (n : ℝ) / 4)) := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact (norm_add_le _ _).trans (by linarith [hb, hb'])
    _ = _ := by rw [← hscale]; ring

/-- A common literal exponential envelope pays both signed prime samples
and the entire prime-power series in the original Weil correlation.
The hypothesis is pointwise convergence of the tests, not convergence of
their arithmetic forms. No zero-side formula, evenness or RH is assumed. -/
theorem complete_prime_correlation_tendsto
    {A : ℝ} (hA : 0 ≤ A) {f : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hc : ∀ k, Continuous (f k)) (hgc : Continuous g)
    (hf : ∀ k x, ‖f k x‖ ≤ A * exp (-|x|))
    (hlim : ∀ x, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    (∀ k, Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
        (weilTest (f k) (f k) (log n) + weilTest (f k) (f k) (-log n)))) ∧
    Summable (fun n : ℕ =>
      ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
        (weilTest g g (log n) + weilTest g g (-log n))) ∧
    Tendsto (fun k => ∑' n : ℕ,
      ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
        (weilTest (f k) (f k) (log n) + weilTest (f k) (f k) (-log n)))
      atTop (𝓝 (∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / sqrt n : ℝ) : ℂ) *
          (weilTest g g (log n) + weilTest g g (-log n)))) := by
  have hgb (x : ℝ) : ‖g x‖ ≤ A * exp (-|x|) :=
    le_of_tendsto' (hlim x).norm (fun k => hf k x)
  have hs := arithmeticEnvelope_summable.mul_left (2 * envelopeConstant A)
  refine ⟨fun k => hs.of_norm_bounded (primeTerm_bound hA (hc k) (hf k)),
    hs.of_norm_bounded (primeTerm_bound hA hgc hgb), ?_⟩
  exact tendsto_tsum_of_dominated_convergence hs
    (fun n => tendsto_const_nhds.mul
      ((correlation_tendsto hA hc hf hlim (log n)).add
        (correlation_tendsto hA hc hf hlim (-log n))))
    (Eventually.of_forall fun k => primeTerm_bound hA (hc k) (hf k))

#print axioms complete_prime_correlation_tendsto

end D5.S3.Weil.ZetaBridge.ExponentialPrimeCorrelationPassage
