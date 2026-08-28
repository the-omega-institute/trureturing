/- GID: D5/S3/AnalyticClosure/ZeroSumGaugeInvariance
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/ZeroSumGaugeInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Absolutely summable local contributions are unchanged by a zero-sum gauge shift. -/

import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators

namespace D5.S3.AnalyticClosure.ZeroSumGaugeInvariance

/- The source local ledger and its gauge shift are represented directly by
   absolutely summable real-valued families. -/
theorem zero_sum_gauge_invariance {V : Type*}
    (localContribution shift : V → ℝ)
    (hLocal : Summable localContribution)
    (hShift : Summable shift)
    (hZero : (∑' v, shift v) = 0) :
    (∑' v, (localContribution v + shift v)) = ∑' v, localContribution v := by
  rw [hLocal.tsum_add hShift, hZero]
  simp

#print axioms zero_sum_gauge_invariance

end D5.S3.AnalyticClosure.ZeroSumGaugeInvariance
