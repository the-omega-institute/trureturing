# Actual mixing and complete-prefix comparison

## Abstract

Actual mixing and complete-prefix comparison.

**Theorem 1.1 (Actual mixing and complete-prefix comparison).**

Lean statement: `D5/S3/TotalVariation/ParryTwistedComparison.parry_mixing_and_complete_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/ParryTwistedComparison.parry_mixing_and_complete_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k >= 2, let p = parryParameter k and pi = parryLaw k. First, for every natural G and state s, the total variation between the G-step row of kernel k p and pi is at most (3/4)^(G/3). Second, for every natural n,G with n+G >= 2, the normalized complete complement-twisted prefix law differs from the pi-weighted stationary prefix law by at most 2(n+G)(3/4)^(G/3) + Real.goldenRatio^(2-(n+G)). Third, for every natural R >= 1, G >= 1, and deterministic table f : (Fin R -> Bool) -> Bool, the absolute difference between the twisted and stationary probabilities of the same defect event is bounded by 2(R+1+G)(3/4)^(G/3) + Real.goldenRatio^(2-(R+1+G)). The event is f(r_1,...,r_R) XOR f(r_0,...,r_(R-1)) XOR NOT r_R, with all relation bits taken from the same complete R+1-transition prefix and the same fixed table f used in both laws. Here G/3 is division rounded down, and the golden-ratio exponents are integers. No small-error premise is assumed.

## References

- Truth anchor: `D5/S3/TotalVariation/ParryTwistedComparison.parry_mixing_and_complete_prefix`
- Dependency: [D5/S3/TotalVariation/DataProcessing](DataProcessing.md)
- Dependency: [D5/S3/TotalVariation/Metric](Metric.md)
- Dependency: [D5/S3/TotalVariation/ParryResetEstimates](ParryResetEstimates.md)
- Dependency: [D5/S3/TotalVariation/TwistedPrefixComparison](TwistedPrefixComparison.md)
