/- GID: D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/VonMangoldtCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids VonMangoldtCount analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/VonMangoldtCount.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount.Integral

/-! Original VonMangoldtCount analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann.VonMangoldtCount

open Complex Finset Filter MeasureTheory Set Asymptotics Metric MeromorphicOn
open scoped Real Topology ArithmeticFunction LSeries.notation

/-- **Global Multiplicity-Weighted Riemann–von Mangoldt Upper Bound Under `RiemannHypothesis`**:
Under `RiemannHypothesis`, for all `6 ≤ t`,
`(weightedZeroCountingFunction t : ℝ) ≤ (16 / 5) * t * Real.log t + (11 / 5) * t`. -/
theorem weightedZeroCountingFunction_le_sixteen_fifths
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 6 ≤ t) :
    (weightedZeroCountingFunction t : ℝ) ≤ (16 / 5) * t * Real.log t + (11 / 5) * t := by
  classical
  let K : ℕ := ⌊(t - 6) / 4⌋₊ + 1
  let W : ℕ → Finset ℂ := fun k ↦
    nontrivialZetaZerosInFourWindow (8 + 4 * (k : ℝ)) ∪
      nontrivialZetaZerosInFourWindow (-(8 + 4 * (k : ℝ)))
  have h_sub : nontrivialZetaZerosUpTo t ⊆ (Finset.range K).biUnion W :=
    nontrivialZetaZerosUpTo_subset_biUnion_fourWindows hRH t
  have h_nat_le :
      weightedZeroCountingFunction t ≤
        ∑ k ∈ Finset.range K, ∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ := by
    unfold weightedZeroCountingFunction
    exact (Finset.sum_le_sum_of_subset h_sub).trans
      (sum_biUnion_range_le_nat K W (analyticOrderNatAt riemannZeta))
  have h_real_le :
      (weightedZeroCountingFunction t : ℝ) ≤
        ∑ k ∈ Finset.range K, ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
    exact_mod_cast h_nat_le
  have ht_pos : 0 < t := by linarith
  have h_log_t_pos : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h_log_two_pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h_wk_bound : ∀ k ∈ Finset.range K,
      ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
        (512 / 41) * (Real.log t + Real.log 2) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk_le : k ≤ ⌊(t - 6) / 4⌋₊ := Nat.le_of_lt_succ hk
    have hk_real : (k : ℝ) ≤ (t - 6) / 4 :=
      (Nat.cast_le.mpr hk_le).trans (Nat.floor_le (by linarith))
    have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h_u_nat := sum_union_le_nat
      (nontrivialZetaZerosInFourWindow (8 + 4 * (k : ℝ)))
      (nontrivialZetaZerosInFourWindow (-(8 + 4 * (k : ℝ))))
      (analyticOrderNatAt riemannZeta)
    have h_u_real :
        ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
          ((∑ ρ ∈ nontrivialZetaZerosInFourWindow (8 + 4 * (k : ℝ)),
            analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) +
          ((∑ ρ ∈ nontrivialZetaZerosInFourWindow (-(8 + 4 * (k : ℝ))),
            analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
      dsimp only [W]
      exact_mod_cast h_u_nat
    have hy1 : 8 ≤ |8 + 4 * (k : ℝ)| := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    have hy2 : 8 ≤ |-(8 + 4 * (k : ℝ))| := by
      rw [abs_neg]
      exact hy1
    have hb1 := sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis hRH hy1
    have hb2 := sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis hRH hy2
    rw [abs_neg] at hb2
    have h_abs_add : |8 + 4 * (k : ℝ)| + 4 ≤ 2 * t := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    have h_log_le : Real.log (|8 + 4 * (k : ℝ)| + 4) ≤ Real.log t + Real.log 2 := by
      have h1 : Real.log (|8 + 4 * (k : ℝ)| + 4) ≤ Real.log (2 * t) :=
        Real.log_le_log (by positivity) h_abs_add
      rw [Real.log_mul (by norm_num) ht_pos.ne'] at h1
      linarith
    linarith
  have h_sum_le :
      (∑ k ∈ Finset.range K, ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ)) ≤
        (K : ℝ) * ((512 / 41) * (Real.log t + Real.log 2)) := by
    calc
      (∑ k ∈ Finset.range K, ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ))
        ≤ ∑ _k ∈ Finset.range K, (512 / 41) * (Real.log t + Real.log 2) :=
          Finset.sum_le_sum h_wk_bound
      _ = (K : ℝ) * ((512 / 41) * (Real.log t + Real.log 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK_le : (K : ℝ) ≤ t / 4 := by
    dsimp only [K]
    push_cast
    have hfl : (⌊(t - 6) / 4⌋₊ : ℝ) ≤ (t - 6) / 4 := Nat.floor_le (by linarith)
    linarith
  have h_prod_le :
      (K : ℝ) * ((512 / 41) * (Real.log t + Real.log 2)) ≤
        (t / 4) * ((512 / 41) * (Real.log t + Real.log 2)) :=
    mul_le_mul_of_nonneg_right hK_le (by positivity)
  have h_log2 := log_two_le_forty_four_div_sixty_three
  nlinarith

/-- Under `RiemannHypothesis`, `weightedZeroCountingFunction T = 0` for all `T ≤ 6`. -/
theorem weightedZeroCountingFunction_eq_zero_of_le_six (hRH : RiemannHypothesis) {T : ℝ}
    (hT : T ≤ 6) :
    weightedZeroCountingFunction T = 0 := by
  unfold weightedZeroCountingFunction
  rw [nontrivialZetaZerosUpTo_eq_empty_of_le_six hRH hT, Finset.sum_empty]

end ConjectureMachines.Semantics.Riemann.VonMangoldtCount
