# Complete Twisted Prefix Comparison

## Abstract

A uniform comparison for complete twisted prefixes under explicit kernel estimates.

**Theorem 1.1 (Length-uniform complete-prefix comparison).**

Lean statement: `D5/S3/TotalVariation/TwistedPrefixComparison.complete_prefix_comparison_of_estimates`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/TwistedPrefixComparison.complete_prefix_comparison_of_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural k,n,G, real p, a mass vector pi : State k -> R, and real epsilon, assume k >= 2, p > 0, n + G >= 2, every row of K = kernel k p sums to one, pi is pointwise nonnegative with total sum one and satisfies pi(flip(s)) = pi(s) for every s, epsilon >= 0, and |(K^G)(s,t) - pi(t)| <= epsilon for every pair of states s,t. Then the total variation between the normalized complete twisted-prefix law twistedLaw k p n G and the pi-weighted n-step path law referenceLaw k p n pi is at most 2(n+G)epsilon plus the pi-mass of states whose suffix is at least n+G. All n transitions remain in the comparison; no assumption that epsilon < 1, stationarity of pi, or a numerical mixing rate is added.

## References

- Truth anchor: `D5/S3/TotalVariation/TwistedPrefixComparison.complete_prefix_comparison_of_estimates`
- Dependency: [D5/S3/TotalVariation/Pinsker](Pinsker.md)
- Dependency: [D5/S3/TotalVariation/TwistedResetPaths](TwistedResetPaths.md)
