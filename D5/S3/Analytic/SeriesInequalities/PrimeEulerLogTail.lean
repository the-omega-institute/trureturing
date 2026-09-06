/- GID: D5/S3/Analytic/SeriesInequalities/PrimeEulerLogTail
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/PrimeEulerLogTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The omitted-prime Euler logarithms have an explicit power-decay tail bound. -/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Nat.Prime.Basic

/- Search: pinned Mathlib supplies the integral comparison, power integral, and log inequality.
   Repository EulerLogBridge gives a whole-series identity; EulerProducts.tsum_succ_rpow_le
   treats the power series at endpoint one. Neither states this logarithmic tail estimate.
   External search: Tavily via NyxID, 2026-09-06, Lean Euler product logarithm tail bound;
   no exact Lean declaration found in the returned results. Preregistration v3 precedes proof.
   This module carries only the omitted-prime error term, not a finite-window error theorem. -/

namespace D5.S3.Analytic.SeriesInequalities.PrimeEulerLogTail

noncomputable section

private def integerLogTail (s : ℝ) (X n : ℕ) : ℝ :=
  if X < n then -Real.log (1 - (n : ℝ) ^ (-s)) else 0

private theorem euler_log_nonneg (s : ℝ) (hs : 1 < s) (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ -Real.log (1 - (n : ℝ) ^ (-s)) := by
  have hnR : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hq : (n : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hnR (by linarith)
  apply neg_nonneg.mpr
  exact Real.log_nonpos (by linarith)
    (sub_le_self _ (Real.rpow_nonneg (Nat.cast_nonneg _) _))

private theorem euler_log_le (s : ℝ) (hs : 1 < s) (n : ℕ) (hn : 2 ≤ n) :
    -Real.log (1 - (n : ℝ) ^ (-s)) ≤
      (1 / (1 - (2 : ℝ) ^ (-s))) * (n : ℝ) ^ (-s) := by
  have htwo : (2 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq : (n : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn) (by linarith)
  have hden : 0 < 1 - (n : ℝ) ^ (-s) := by linarith
  have hden2 : 0 < 1 - (2 : ℝ) ^ (-s) := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  rw [Real.log_inv] at hlog
  calc
    -Real.log (1 - (n : ℝ) ^ (-s)) ≤ (1 - (n : ℝ) ^ (-s))⁻¹ - 1 := hlog
    _ = (n : ℝ) ^ (-s) / (1 - (n : ℝ) ^ (-s)) := by field_simp; ring
    _ ≤ (n : ℝ) ^ (-s) / (1 - (2 : ℝ) ^ (-s)) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hden2 (by linarith)
    _ = _ := by ring

private theorem integerLogTail_nonneg (s : ℝ) (hs : 1 < s) (X : ℕ) (hX : 2 ≤ X)
    (n : ℕ) : 0 ≤ integerLogTail s X n := by
  unfold integerLogTail
  split_ifs with hn
  · exact euler_log_nonneg s hs n (by omega)
  · exact le_rfl

private theorem integerLogTail_summable (s : ℝ) (hs : 1 < s) (X : ℕ) (hX : 2 ≤ X) :
    Summable (integerLogTail s X) := by
  apply Summable.of_nonneg_of_le (integerLogTail_nonneg s hs X hX) _
    ((Real.summable_nat_rpow.mpr (by linarith : -s < -1)).mul_left
      (1 / (1 - (2 : ℝ) ^ (-s))))
  intro n
  unfold integerLogTail
  split_ifs with hn
  · exact euler_log_le s hs n (by omega)
  · have htwo : (2 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact mul_nonneg (one_div_nonneg.mpr (by linarith))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

private theorem integer_log_tail_le (s : ℝ) (hs : 1 < s) (X : ℕ) (hX : 2 ≤ X) :
    (∑' n : ℕ, integerLogTail s X n) ≤
      1 / (1 - (2 : ℝ) ^ (-s)) * ((X : ℝ) ^ (1 - s) / (s - 1)) := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have htwo : (2 : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc : 0 ≤ 1 / (1 - (2 : ℝ) ^ (-s)) := one_div_nonneg.mpr (by linarith)
  have hexp : -s < -1 := by linarith
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-s)) (Set.Ici (X : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hXR.trans_le hx) hxy (by linarith)
  have hpower := AntitoneOn.tsum_comp_add_le_integral X hanti
    (integrableOn_Ioi_rpow_of_lt hexp hXR)
    (fun t ht => Real.rpow_nonneg (hXR.trans ht).le _)
  rw [integral_Ioi_rpow_of_lt hexp hXR,
    show -s + 1 = -(s - 1) by ring, neg_div_neg_eq] at hpower
  have hsplit := (integerLogTail_summable s hs X hX).sum_add_tsum_nat_add (X + 1)
  have hprefix : ∑ n ∈ Finset.range (X + 1), integerLogTail s X n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnx : ¬ X < n := by have := Finset.mem_range.mp hn; omega
    simp only [integerLogTail, if_neg hnx]
  rw [hprefix, zero_add] at hsplit
  rw [← hsplit]
  have hshift : Summable (fun n : ℕ => ((n + X + 1 : ℕ) : ℝ) ^ (-s)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (X + 1)).mpr (Real.summable_nat_rpow.mpr hexp)
  calc
    (∑' n : ℕ, integerLogTail s X (n + (X + 1))) ≤
        ∑' n : ℕ, (1 / (1 - (2 : ℝ) ^ (-s))) * ((n + X + 1 : ℕ) : ℝ) ^ (-s) := by
      apply Summable.tsum_le_tsum _
        ((summable_nat_add_iff (X + 1)).mpr (integerLogTail_summable s hs X hX))
        (hshift.mul_left _)
      intro n
      simpa only [integerLogTail, if_pos (by omega : X < n + (X + 1)), Nat.add_assoc]
        using euler_log_le s hs (n + X + 1) (by omega)
    _ = (1 / (1 - (2 : ℝ) ^ (-s))) *
        (∑' n : ℕ, ((n + X + 1 : ℕ) : ℝ) ^ (-s)) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [neg_sub] using hpower) hc

/-- The omitted prime directions of an Euler product have an explicit logarithmic tail bound. -/
theorem prime_euler_log_tail_le (s : ℝ) (hs : 1 < s) (X : ℕ) (hX : 2 ≤ X) :
    (∑' p : Nat.Primes, if X < p.val then
      -Real.log (1 - (p.val : ℝ) ^ (-s)) else 0) ≤
      1 / (1 - (2 : ℝ) ^ (-s)) * ((X : ℝ) ^ (1 - s) / (s - 1)) := by
  exact (Summable.tsum_subtype_le (integerLogTail s X) {p : ℕ | p.Prime}
    (integerLogTail_nonneg s hs X hX) (integerLogTail_summable s hs X hX)).trans
    (integer_log_tail_le s hs X hX)

end

end D5.S3.Analytic.SeriesInequalities.PrimeEulerLogTail
