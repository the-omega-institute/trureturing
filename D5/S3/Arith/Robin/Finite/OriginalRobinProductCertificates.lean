/- GID: D5/S3/Arith/Robin/Finite/OriginalRobinProductCertificates
   generality: I
   mirror-B: none(waiver:internal-row-certificate)
   mirror-E: none(waiver:exact-rational-certificates)
   anchors: []
   utility: none
   digest: Balanced natural products certify the gain and height comparisons for the Robin checker. -/

import D5.S3.Arith.Robin.Finite.OriginalRobinBalancedRow35

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate.KernelProducts

/-- Rewrite the exact gain inequality using balanced integer products. -/
theorem row_gain {r : Row} (hc : r.cuts[0]! < 267 * 267) {num den : ℕ}
    (hden : 0 < den) (hval : r.gainUpper = (num : ℚ) / (den : ℚ))
    (h : rowSigma r * den ≤ num * rowOptimizer r) :
    (r.sigmaProduct : ℚ) ≤ r.gainUpper * (r.optimizer : ℚ) := by
  rw [row_sigma hc, row_optimizer hc, hval]
  exact gain_of_nat hden h

/-- Split the height power before kernel reduction of the integer inequality. -/
theorem row_height {r : Row} (hc : r.cuts[0]! < 267 * 267) {num den : ℕ}
    (hden : 0 < den) (hval : r.heightMantissa = (num : ℚ) / (den : ℚ))
    (h : (((2 : ℕ) ^ 256) ^ (r.heightExponent / 256) * 2 ^ (r.heightExponent % 256)) * num ≤
      rowOptimizer r * den) :
    (2 : ℚ) ^ r.heightExponent * r.heightMantissa ≤ (r.optimizer : ℚ) := by
  rw [row_optimizer hc, hval]
  apply height_of_nat hden
  have hs : (2 : ℕ) ^ r.heightExponent =
      ((2 : ℕ) ^ 256) ^ (r.heightExponent / 256) * 2 ^ (r.heightExponent % 256) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  rw [hs]
  exact h

end D5.S3.Arith.Robin.Finite.OriginalRobinRowCertificate.KernelProducts
