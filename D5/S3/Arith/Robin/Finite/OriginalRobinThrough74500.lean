/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinThrough74500
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Finite/OriginalRobinThrough74500
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: The pinned finite certificates prove Robin for every integer above 5040 through log height 74500. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinRows32Through34

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate

open D5.S3.Arith.Robin.ActualRobinInterval
open D5.S3.Weil.GronwallLowerEnvelope

/-- The pinned numerical certificates prove the original Robin inequality up to log height
74500, the starting point of the explicit analytic estimate. -/
theorem original_robin_through_74500 {n : ℕ} (hn : 5040 < n)
    (hhi : Real.log (n : ℝ) ≤ 74500) :
    (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  apply original_robin_of_margin (by omega)
  apply pinnedRow35_checks.extend (by omega)
  · intro height
    apply robin_margin_through_pinned_row34 hn
    simpa [pinnedRow35, pinnedRow34] using height
  · exact hhi.trans (by norm_num [pinnedRow35])

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate
