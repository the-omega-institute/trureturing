/- GID: D5/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/AllSupport/RobinLargeHeightMargin
   mirror-E: none(waiver:explicit-Robin-margin)
   anchors: []
   utility: none
   digest: Under RH the normalized original Robin margin strictly exceeds 17/500 above log height 74500. -/

import D5.S3.Arith.Robin.AllSupport.RobinPrimeCost74500
import D5.S3.Arith.Robin.AllSupport.RobinSignedTail74500
import D5.S3.Arith.Robin.Finite.OriginalRobinThrough74500

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.AllSupport

open D5.S3.Arith.Robin.ActualRobinInterval (original_robin_of_margin)
open D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate (original_robin_through_74500)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)

/-- The actual all-support arithmetic and signed analytic estimates leave a uniform
strict reserve in the normalized log margin above the finite window. -/
theorem normalized_robinLogMargin_large_gt (hRH : RiemannHypothesis) {n : ℕ}
    (hn : 0 < n) (hheight : 74500 ≤ Real.log (n : ℝ)) :
    (17 / 500 : ℝ) <
      (Real.sqrt (Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ))) * robinLogMargin n := by
  let H := Real.log (n : ℝ)
  have hH : 74500 ≤ H := hheight
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith only [hH])
  have hscale : 0 ≤ Real.sqrt H * Real.log H := mul_nonneg (Real.sqrt_nonneg H) hlog
  have hledger : primeCost H + thetaTail H ≤ robinLogMargin n :=
    robin_margin_ge_prime_cost_add_theta_tail hn (by change 2 ≤ H; linarith only [hH])
  have hscaled := mul_le_mul_of_nonneg_left hledger hscale
  rw [mul_add] at hscaled
  have hcost := primeCost_normalized_lower hRH hH
  have htail := normalized_neg_thetaTail_lt_223_div_100 hRH hH
  change (17 / 500 : ℝ) < (Real.sqrt H * Real.log H) * robinLogMargin n
  linarith only [hcost, htail, hscaled]

/-- The original inequality follows from RH by the finite certificates and
the quantitative all-support estimate. -/
theorem original_robin_of_rh_all_support (hRH : RiemannHypothesis) {n : ℕ}
    (hn : 5040 < n) : (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  rcases le_total (Real.log (n : ℝ)) 74500 with h | h
  · exact original_robin_through_74500 hn h
  · apply original_robin_of_margin (by omega)
    have hscale : 0 ≤ Real.sqrt (Real.log (n : ℝ)) * Real.log (Real.log (n : ℝ)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by linarith only [h]))
    have hmargin := normalized_robinLogMargin_large_gt hRH (show 0 < n by omega) h
    by_contra! hnpos
    have := mul_nonpos_of_nonneg_of_nonpos hscale hnpos
    linarith only [hmargin, this]

end D5.S3.Arith.Robin.AllSupport
