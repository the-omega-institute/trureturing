/- GID: D5/S3/Arith/Robin/PriceRecord/CompleteSignedLedger
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/CompleteSignedLedger
   mirror-E: none(waiver:analytic-identity)
   anchors: []
   utility: none
   digest: Exact full signed Mangoldt Mertens Euler ledger at the same integer and cutoff. -/

import D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
import D5.S3.Arith.Robin.CompleteMertensPeak
import D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus
import D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion

/-! The exact complete signed ledger and its same-minimum negative-tail consequence. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
open Finset
open scoped BigOperators
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.GronwallLowerEnvelope
open D5.S3.Arith.Robin.PriceRecord.NonlinearPrimeExclusion
open D5.S3.Arith.Robin.PriceRecord.ActualBalancedCutoff
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.ActualGlobalBracketing


/-- Exact equality, retaining the literal full weighted tail and the SAME N,z. -/
theorem robin_margin_eq_complete_signed_ledger {z : ℝ} (hz : 4 ≤ z) {N : ℕ}
    (hN : 0 < N) (hsupport : N.primeFactors = Nat.primesLE ⌊z⌋₊) :
    let M := Real.log (N : ℝ) - z
    robinLogMargin N =
      D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail psiErrorKernel z +
      (tail N + (Real.log (N : ℝ) - Chebyshev.psi z) / (z * Real.log z) -
        fullPrimePowerResidual z) -
      (Real.log (Real.log z) + M / (z * Real.log z) -
        Real.log (Real.log (z + M))) := by
  have hres := complete_mangoldt_add_E3_eq_neg_residual hz
  have hledger := (complete_mertens_ledger (by linarith : 2 ≤ z)).2.2
  have heuler : eulerMass N = Real.eulerMascheroniConstant + Real.log (Real.log z) -
      Mertens.E₃ z := by
    simp only [eulerMass, hsupport, Mertens.E₃,
      Nat.primesLE_eq_filter_Ioc_zero, one_div, sum_neg_distrib]
    ring
  dsimp only
  rw [show z + (Real.log (N : ℝ) - z) = Real.log (N : ℝ) by ring]
  unfold robinLogMargin
  rw [log_sigma_div_eq_eulerMass_sub_tail hN, heuler]
  simp only [sub_div] at hledger ⊢
  linarith only [hres, hledger]

/-- The sole original nonpositive failure gives a strictly negative FULL
weighted tail at the SAME attained minimum and cutoff, retaining every
optimizer, tie, support, half-shift and nonlinear prime-gap conclusion. -/
theorem failure_has_negative_complete_weighted_tail
    (hfailure : ∃ n : ℕ, 5040 < n ∧ robinLogMargin n ≤ 0) :
    ∃ (N : ℕ) (z : ℝ), 55440 < N ∧ robinLogMargin N ≤ 0 ∧
      (∀ m : ℕ, 5040 < m → robinLogMargin N ≤ robinLogMargin m) ∧
      0 < price (Real.log N) ∧ price (Real.log N) < boundaryPrice ∧
      IsGoldenResourceOptimal (price (Real.log N)) N ∧
      (∀ m : ℕ, 1 ≤ m → m ≠ N →
        goldenResourceObjective (price (Real.log N)) m <
          goldenResourceObjective (price (Real.log N)) N) ∧
      N = strictInteger (price (Real.log N)) ∧
      N = maximalInteger (price (Real.log N)) ∧
      (∀ p k : ℕ, p.Prime → 1 ≤ k →
        price (Real.log N) ≠ goldenLayerMarginal p k) ∧
      11 < z ∧ 0 < Real.log N - z ∧ Real.log N - z < 1 / 2 ∧
      firstLayerPrice z = 1 / (Real.log N * Real.log (Real.log N)) ∧
      (∀ t : ℝ, 1 < t →
        firstLayerPrice t = 1 / (Real.log N * Real.log (Real.log N)) → t = z) ∧
      N.primeFactors = Nat.primesLE ⌊z⌋₊ ∧
      (∃ α β : ℝ, NonlinearPrimeGap N z α β) ∧
      D5.S3.Weil.Mertens.WeightedTailTransport.weightedTail
        D5.S3.Arith.Robin.CompleteMertensPeak.psiErrorKernel z <
          -1 / (4000 * Real.sqrt z * Real.log z) := by
  obtain ⟨N, z, hN, hSN, hmin, hp0, hpb, hopt, hstrict, hNs, hNm, hnotie,
    hz, hM0, hMhalf, hroot, hunique, hsupport, hgap⟩ :=
      failure_has_nonlinear_prime_gap hfailure
  refine ⟨N, z, hN, hSN, hmin, hp0, hpb, hopt, hstrict, hNs, hNm, hnotie,
    hz, hM0, hMhalf, hroot, hunique, hsupport, hgap, ?_⟩
  have hN0 : 0 < N := by omega
  have hmargin := robin_margin_eq_complete_signed_ledger (by linarith : 4 ≤ z) hN0 hsupport
  have hsurplus :=
    D5.S3.Arith.Robin.PriceRecord.CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_sub_curvature_root_scale
      hz hM0 hMhalf hN0 hsupport
  dsimp only at hmargin hsurplus
  rw [neg_div]
  linarith only [hmargin, hsurplus, hSN]


end D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
