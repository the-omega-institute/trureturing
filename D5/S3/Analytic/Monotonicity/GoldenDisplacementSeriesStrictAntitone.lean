/- GID: D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesStrictAntitone
   generality: I
   mirror-B: D5/B/S3/Analytic/Monotonicity/GoldenDisplacementSeriesStrictAntitone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A strict coordinate increase strictly lowers the golden displacement sum. -/

/- Library-search audit trail (2026-08-27):
* Searches of `D5/**/*.lean` for `dTerm`, `nS 2`, strict sum comparison, and
  parameter order found the frozen private termwise lemma in the earlier frozen non-strict
  companion, the public `nS_prime_pow` computation, and no public termwise parameter-order
  theorem.
* Searches of pinned `Mathlib/**/*.lean` found the exact strict-series theorem
  `Summable.tsum_lt_tsum_of_nonneg` and the base-greater-than-one branch
  `Real.rpow_lt_rpow_of_exponent_lt`; both are used directly below.
* The public `goldenSubstStart_one_eq_two` gives the strict witness `nS 2 = 4`.
  Index two is chosen because both real-power bases are then strictly greater than one.
* The exported termwise lemma is the authoritative usable home for the second consumer.
  The earlier frozen non-strict companion keeps its own private copy: revoking a valid
  frozen node is an errata remedy, not an API-refactoring mechanism.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure

open GoldenDesubstitutionLength
open GoldenDisplacementEulerProduct
open GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure

namespace D5.S3.Analytic.Monotonicity.GoldenDisplacementSeriesStrictAntitone

noncomputable section

/-- Increasing both parameters coordinatewise cannot increase any displacement term. -/
lemma dTerm_le_of_parameters_le {s1 w1 s2 w2 : ℝ}
    (hs : s1 ≤ s2) (hw : w1 ≤ w2) (n : ℕ) :
    dTerm s2 w2 n ≤ dTerm s1 w1 n := by
  by_cases hn : n = 0
  · subst n
    rw [dTerm_zero, dTerm_zero]
  · have hnOneNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnOne : (1 : ℝ) ≤ n := by
      exact_mod_cast hnOneNat
    have hnSOne : (1 : ℝ) ≤ nS n := by
      exact_mod_cast hnOneNat.trans (le_nS hn)
    unfold dTerm
    rw [if_neg hn, if_neg hn]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hnSOne (neg_le_neg hs))
      (Real.rpow_le_rpow_of_exponent_le hnOne (neg_le_neg hw))
      (by positivity) (by positivity)

private lemma dTerm_lt_at_two {s1 w1 s2 w2 : ℝ}
    (hs : s1 ≤ s2) (hw : w1 ≤ w2) (hstrict : s1 < s2 ∨ w1 < w2) :
    dTerm s2 w2 2 < dTerm s1 w1 2 := by
  have hnS2 : nS 2 = 4 := by
    rw [show (2 : ℕ) = 2 ^ 1 by norm_num, nS_prime_pow Nat.prime_two 1,
      goldenSubstStart_one_eq_two]
    norm_num
  simp only [dTerm, if_neg (by norm_num : (2 : ℕ) ≠ 0), hnS2, Nat.cast_ofNat]
  rcases hstrict with hslt | hwlt
  · have hsPow : (4 : ℝ) ^ (-s2) < (4 : ℝ) ^ (-s1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hslt)
    have hwPow : (2 : ℝ) ^ (-w2) ≤ (2 : ℝ) ^ (-w1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hw)
    calc
      (4 : ℝ) ^ (-s2) * (2 : ℝ) ^ (-w2) ≤
          (4 : ℝ) ^ (-s2) * (2 : ℝ) ^ (-w1) :=
        mul_le_mul_of_nonneg_left hwPow (by positivity)
      _ < (4 : ℝ) ^ (-s1) * (2 : ℝ) ^ (-w1) :=
        mul_lt_mul_of_pos_right hsPow (by positivity)
  · have hsPow : (4 : ℝ) ^ (-s2) ≤ (4 : ℝ) ^ (-s1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hs)
    have hwPow : (2 : ℝ) ^ (-w2) < (2 : ℝ) ^ (-w1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hwlt)
    calc
      (4 : ℝ) ^ (-s2) * (2 : ℝ) ^ (-w2) <
          (4 : ℝ) ^ (-s2) * (2 : ℝ) ^ (-w1) :=
        mul_lt_mul_of_pos_left hwPow (by positivity)
      _ ≤ (4 : ℝ) ^ (-s1) * (2 : ℝ) ^ (-w1) :=
        mul_le_mul_of_nonneg_right hsPow (by positivity)

/-- A coordinatewise parameter increase that is strict in either coordinate strictly lowers
the golden displacement sum. Only summability at the original pair is required. -/
theorem golden_displacement_series_strict_antitone {s1 w1 s2 w2 : ℝ}
    (hs : s1 ≤ s2) (hw : w1 ≤ w2) (hstrict : s1 < s2 ∨ w1 < w2)
    (hsum1 : Summable (dTerm s1 w1)) :
    (∑' n : ℕ, dTerm s2 w2 n) < ∑' n : ℕ, dTerm s1 w1 n := by
  exact Summable.tsum_lt_tsum_of_nonneg
    (i := 2) (dTerm_nonneg s2 w2)
    (dTerm_le_of_parameters_le hs hw)
    (dTerm_lt_at_two hs hw hstrict) hsum1

end

end D5.S3.Analytic.Monotonicity.GoldenDisplacementSeriesStrictAntitone
