/- GID: D5/S3/Analytic/KummerRatio/Transform
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Transform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum, mathlib/module/Mathlib.Analysis.Normed.Ring.InfiniteSum, mathlib/module/Mathlib.Analysis.SpecialFunctions.Exponential]
   utility: none
   digest: Finite Pochhammer coefficient identities for Kummer reflection. -/

import D5.S3.Analytic.KummerRatio.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential

open Finset

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

end D5.S3.Analytic.KummerRatio.Transform
