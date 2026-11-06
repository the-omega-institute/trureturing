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

set_option autoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
open Finset
open scoped BigOperators
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail
open D5.S3.Arith.Robin.PriceRecord.FullPrimePowerArithmeticSurplus
open D5.S3.Arith.Robin.CompleteMertensPeak
open D5.S3.Weil.GronwallLowerEnvelope

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

end D5.S3.Arith.Robin.PriceRecord.CompleteSignedLedger
