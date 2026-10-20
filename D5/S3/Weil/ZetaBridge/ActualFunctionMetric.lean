/- GID: D5/S3/Weil/ZetaBridge/ActualFunctionMetric
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualFunctionMetric
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Integral function metric coercivity of the actual paired energy for arbitrary complex polynomials. -/

import D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Polynomial MeasureTheory
open scoped Interval ComplexConjugate
namespace D5.S3.Weil.ZetaBridge.ActualFunctionMetric
open D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
open D5.S3.Weil.ZetaBridge.ActualReciprocalEnclosure
open D5.S3.Weil.ZetaBridge.ActualPairedReciprocal
open D5.S3.Analytic.PolynomialReciprocalBounds

def mu0 : ℝ := (Real.log (2:ℝ))^2/4
def gamma : ℝ := Real.pi/4
def kappa0 : ℝ := mu0/(1+gamma^2+mu0)

private lemma mu0_lower : (1:ℝ)/16 ≤ mu0 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  have hlog : (1:ℝ)/2 ≤ Real.log (2:ℝ) := by
    norm_num at h
    exact h
  unfold mu0
  nlinarith only [hlog,sq_nonneg (Real.log (2:ℝ)-(1:ℝ)/2)]

private lemma mu0_pos : 0 < mu0 := lt_of_lt_of_le (by norm_num) mu0_lower
lemma kappa0_gt : (1:ℝ)/33 < kappa0 := by
  have hg : 0 < gamma := by unfold gamma; positivity
  have hg1 : gamma < 1 := by unfold gamma; nlinarith only [Real.pi_lt_four]
  have hden : 0 < 1+gamma^2+mu0 := by nlinarith [sq_nonneg gamma, mu0_pos]
  unfold kappa0
  apply (lt_div_iff₀ hden).2
  nlinarith only [mu0_lower,mul_pos (sub_pos.mpr hg1) (show 0 < 1+gamma by positivity)]

/-- A two by two function metric bound, proved by an exact sum of squares. -/
private lemma metric_point {c : ℕ} (hc : 3 ≤ c) (a b : ℂ) :
    kappa0*(‖a‖^2+‖b‖^2) ≤ ‖a+(gamma:ℂ)*b‖^2+mean c*‖b‖^2 := by
  have hmu : mu0 ≤ mean c := prime_symbol_mean_lower_bound hc
  have hden : 0 < 1+gamma^2+mu0 := by nlinarith [sq_nonneg gamma, mu0_pos]
  have he : (1+gamma^2+mu0)*(‖a+(gamma:ℂ)*b‖^2+mu0*‖b‖^2)-
      mu0*(‖a‖^2+‖b‖^2) =
      ‖a+(gamma:ℂ)*b‖^2+‖(gamma:ℂ)*a+((gamma^2+mu0:ℝ):ℂ)*b‖^2 := by
    simp only [norm_square_real_add]
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im]
    ring
  have hs : mu0*(‖a‖^2+‖b‖^2) ≤
      (1+gamma^2+mu0)*(‖a+(gamma:ℂ)*b‖^2+mu0*‖b‖^2) := by
    have hnon := add_nonneg (sq_nonneg ‖a+(gamma:ℂ)*b‖)
      (sq_nonneg ‖(gamma:ℂ)*a+((gamma^2+mu0:ℝ):ℂ)*b‖)
    linarith only [he,hnon]
  calc
    _ = (mu0*(‖a‖^2+‖b‖^2))/(1+gamma^2+mu0) := by unfold kappa0; ring
    _ ≤ ‖a+(gamma:ℂ)*b‖^2+mu0*‖b‖^2 := (div_le_iff₀ hden).2 (by simpa only [mul_comm] using hs)
    _ ≤ _ := add_le_add (le_refl (‖a+(gamma:ℂ)*b‖^2))
      (mul_le_mul_of_nonneg_right hmu (sq_nonneg ‖b‖))

/-- The exact function norm coercivity, without a monomial/Hilbert conversion. -/
theorem actual_paired_function_metric {c : ℕ} (hc : 3 ≤ c) (A B : ℂ[X]) :
    kappa0*(∫ t in (-1:ℝ)..1, (‖value A t‖^2+‖value B t‖^2)) ≤ pairedEnergy c A B := by
  let E : ℝ → ℝ := fun t => ‖value A t‖^2+‖value B t‖^2
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hreflection : (∫ t in (0:ℝ)..1, E t+E (-t)) = ∫ t in (-1:ℝ)..1, E t := by
    have hi1 : IntervalIntegrable E volume 0 1 := hE.intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun t : ℝ => E (-t)) volume 0 1 :=
      (hE.comp continuous_neg).intervalIntegrable 0 1
    rw [intervalIntegral.integral_add hi1 hi2,intervalIntegral.integral_comp_neg]
    simp only [neg_zero]
    rw [add_comm,intervalIntegral.integral_add_adjacent_intervals
      (hE.intervalIntegrable (-1) 0) (hE.intervalIntegrable 0 1)]
  rw [← hreflection,← intervalIntegral.integral_const_mul,pairedEnergy_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((continuous_const.mul (hE.add (hE.comp continuous_neg))).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun t : ℝ =>
      ‖value A t+((Real.pi/4:ℝ):ℂ)*value B t‖^2+
      ‖value A (-t)-((Real.pi/4:ℝ):ℂ)*value B (-t)‖^2+
      mean c*(‖value B t‖^2+‖value B (-t)‖^2))).intervalIntegrable 0 1)
  intro t _
  have hp := metric_point hc (value A t) (value B t)
  have hm := metric_point hc (value A (-t)) (-value B (-t))
  simp only [norm_neg,mul_neg,← sub_eq_add_neg] at hm
  dsimp only [E, Pi.mul_apply, Pi.add_apply, Function.comp_apply]
  unfold gamma at hp hm
  nlinarith only [hp,hm]

end D5.S3.Weil.ZetaBridge.ActualFunctionMetric
