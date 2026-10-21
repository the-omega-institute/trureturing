/- GID: D5/S3/Analytic/KummerRatio/Transform
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Transform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum, mathlib/module/Mathlib.Analysis.Normed.Ring.InfiniteSum, mathlib/module/Mathlib.Analysis.SpecialFunctions.Exponential]
   utility: none
   digest: Kummer reflection by finite Pochhammer identities and the entire series Cauchy product. -/

import D5.S3.Analytic.KummerRatio.Series
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential

open Finset
open D5.S3.Analytic.KummerRatio.Defs D5.S3.Analytic.KummerRatio.Series

namespace D5.S3.Analytic.KummerRatio.Transform

private lemma poch_shift (s : ℝ) (n : ℕ) :
    (ascPochhammer ℝ (n + 1)).eval s = s * (ascPochhammer ℝ n).eval (s + 1) := by
  rw [ascPochhammer_succ_left]
  simp

private lemma binomial_pochhammer (n : ℕ) (s c : ℝ) (hc : 0 < c) :
    (∑ k ∈ range (n + 1), (n.choose k : ℝ) *
      ((-1 : ℝ)^k * ((ascPochhammer ℝ k).eval s / (ascPochhammer ℝ k).eval c))) =
    (ascPochhammer ℝ n).eval (c - s) / (ascPochhammer ℝ n).eval c := by
  induction n generalizing s c with
  | zero => simp
  | succ n ih =>
    rw [sum_choose_succ_mul (fun k _ => (-1 : ℝ)^k *
      ((ascPochhammer ℝ k).eval s / (ascPochhammer ℝ k).eval c)) n]
    have hshift (k : ℕ) :
        (-1 : ℝ) ^ (k + 1) *
          ((ascPochhammer ℝ (k + 1)).eval s / (ascPochhammer ℝ (k + 1)).eval c) =
        -(s / c) * ((-1 : ℝ) ^ k *
          ((ascPochhammer ℝ k).eval (s + 1) / (ascPochhammer ℝ k).eval (c + 1))) := by
      rw [poch_shift, poch_shift, pow_succ]
      ring
    simp_rw [hshift]
    simp_rw [show ∀ k : ℕ, (n.choose k : ℝ) * (-(s / c) *
      ((-1 : ℝ) ^ k * ((ascPochhammer ℝ k).eval (s + 1) /
      (ascPochhammer ℝ k).eval (c + 1)))) = -(s / c) *
      ((n.choose k : ℝ) * ((-1 : ℝ) ^ k * ((ascPochhammer ℝ k).eval (s + 1) /
      (ascPochhammer ℝ k).eval (c + 1)))) by intro k; ring]
    rw [← mul_sum, ih (s + 1) (c + 1) (by linarith), ih s c hc]
    rw [show c + 1 - (s + 1) = c - s by ring]
    rw [ascPochhammer_succ_eval, poch_shift]
    have hn : (ascPochhammer ℝ n).eval c ≠ 0 := (ascPochhammer_pos n c hc).ne'
    have hn' : (ascPochhammer ℝ n).eval (c + 1) ≠ 0 :=
      (ascPochhammer_pos n (c + 1) (by linarith)).ne'
    have hrel : c * (ascPochhammer ℝ n).eval (c + 1) =
        (ascPochhammer ℝ n).eval c * (c + n) := (poch_shift c n).symm.trans (ascPochhammer_succ_eval n c)
    field_simp
    linear_combination (ascPochhammer ℝ n).eval (c - s) * hrel

private lemma cauchy_coefficient (s c x : ℝ) (hc : 0 < c) (n : ℕ) :
    (∑ k ∈ range (n + 1),
      (kummerCoeff (c - s) c k * (-x)^k) * (x^(n-k) / ((n-k).factorial : ℝ))) =
      kummerCoeff s c n * x^n := by
  have he (k : ℕ) (hk : k ∈ range (n + 1)) :
      (kummerCoeff (c - s) c k * (-x)^k) * (x^(n-k) / ((n-k).factorial : ℝ)) =
        (x^n / (n.factorial : ℝ)) * ((n.choose k : ℝ) *
          ((-1 : ℝ)^k * ((ascPochhammer ℝ k).eval (c-s) / (ascPochhammer ℝ k).eval c))) := by
    have hkn : k ≤ n := by simpa using hk
    have hfac : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n-k).factorial : ℝ) = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    have hdiv : 1 / ((k.factorial : ℝ) * ((n-k).factorial : ℝ)) =
        (n.choose k : ℝ) / (n.factorial : ℝ) := by
      apply (div_eq_div_iff (by positivity) (by positivity)).2
      simpa [mul_assoc] using hfac.symm
    calc
      _ = ((ascPochhammer ℝ k).eval (c-s) / (ascPochhammer ℝ k).eval c) *
          (-1 : ℝ)^k * (x^k * x^(n-k)) *
            (1 / ((k.factorial : ℝ) * ((n-k).factorial : ℝ))) := by
        rw [neg_pow]
        simp only [kummerCoeff]
        ring
      _ = _ := by
        rw [← pow_add, Nat.add_sub_of_le hkn, hdiv]
        ring
  rw [sum_congr rfl he, ← mul_sum, binomial_pochhammer n (c-s) c hc]
  rw [show c - (c-s) = s by ring]
  simp only [kummerCoeff]
  ring

/-- Reflection of the argument complements the upper parameter. -/
theorem kummer_transform (s : ℝ) (hc : 0 < c) (x : ℝ) :
    kummer s c x = Real.exp x * kummer (c-s) c (-x) := by
  have h1 := (summable_kummer (c-s) c (-x) hc).abs
  have h2 := (Real.summable_pow_div_factorial x).abs
  symm
  rw [mul_comm (Real.exp x), kummer, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
    (by simpa only [Real.norm_eq_abs] using h1) (by simpa only [Real.norm_eq_abs] using h2)]
  exact tsum_congr (cauchy_coefficient s c x hc)

end D5.S3.Analytic.KummerRatio.Transform
