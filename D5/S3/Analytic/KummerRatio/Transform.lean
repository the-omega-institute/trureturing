/- GID: D5/S3/Analytic/KummerRatio/Transform
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Transform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial, mathlib/module/Mathlib.Data.Nat.Choose.Sum, mathlib/module/Mathlib.Analysis.Normed.Ring.InfiniteSum, mathlib/module/Mathlib.Analysis.SpecialFunctions.Exponential]
   utility: none
   digest: Kummer reflection by finite Pochhammer identities and the entire series Cauchy product. -/

import D5.S3.Analytic.KummerRatio.Series
import Mathlib.RingTheory.Binomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential

open Finset
open D5.S3.Analytic.KummerRatio.Defs D5.S3.Analytic.KummerRatio.Series

namespace D5.S3.Analytic.KummerRatio.Transform

private lemma binomial_pochhammer (n : ℕ) (s c : ℝ) (hc : 0 < c) :
    (∑ k ∈ range (n + 1), (n.choose k : ℝ) *
      ((-1 : ℝ)^k * ((ascPochhammer ℝ k).eval s / (ascPochhammer ℝ k).eval c))) =
    (ascPochhammer ℝ n).eval (c - s) / (ascPochhammer ℝ n).eval c := by
  have hcast (x : ℝ) (m : ℕ) :
      (descPochhammer ℤ m).smeval x = (descPochhammer ℝ m).eval x := by
    rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval, descPochhammer_eval_eq_ascPochhammer]
  have hv := Ring.descPochhammer_smeval_add (r := -s) (s := c + (n : ℝ) - 1)
    n (Commute.all _ _)
  simp only [hcast, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hv
  rw [descPochhammer_eval_eq_ascPochhammer] at hv
  have harg : -s + (c + (n : ℝ) - 1) - (n : ℝ) + 1 = c - s := by ring
  rw [harg] at hv
  have hn : (ascPochhammer ℝ n).eval c ≠ 0 := (ascPochhammer_pos n c hc).ne'
  rw [hv, sum_div]
  apply sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa using hk
  have hk0 : (ascPochhammer ℝ k).eval c ≠ 0 := (ascPochhammer_pos k c hc).ne'
  have hneg : (descPochhammer ℝ k).eval (-s) =
      (-1 : ℝ)^k * (ascPochhammer ℝ k).eval s := by
    have h := ascPochhammer_eval_neg_eq_descPochhammer ℝ (-s) k
    simp only [neg_neg] at h
    rw [h]
    simp [← mul_assoc, ← mul_pow]
  have hshift : (descPochhammer ℝ (n-k)).eval (c + (n : ℝ) - 1) =
      (ascPochhammer ℝ (n-k)).eval (c + k) := by
    rw [descPochhammer_eval_eq_ascPochhammer, Nat.cast_sub hkn]
    congr 1
    ring
  have hmul : (ascPochhammer ℝ k).eval c *
      (ascPochhammer ℝ (n-k)).eval (c + k) = (ascPochhammer ℝ n).eval c := by
    have h := congrArg (Polynomial.eval c) (ascPochhammer_mul ℝ k (n-k))
    simpa [Polynomial.eval_mul, Polynomial.eval_comp, Nat.add_sub_of_le hkn] using h
  rw [hneg, hshift]
  field_simp
  linear_combination -(n.choose k : ℝ) * (ascPochhammer ℝ k).eval s * hmul

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
