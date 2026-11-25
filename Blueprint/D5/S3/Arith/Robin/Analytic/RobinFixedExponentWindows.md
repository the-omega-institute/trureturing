# Logarithmic saving under a cofinal one-sided bound

## Abstract

Signed mass comparison from a fixed Mangoldt exponent

**Theorem 1.1 (The normalized weighted and unweighted masses).**

$$|Mw - Mq| \le \frac{K}{kappa \cdot \operatorname{log}\left(A\right)} \cdot (B^{kappa} - A^{kappa})$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/RobinFixedExponentWindows.signed_mass_comparison_of_frequently_window_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix 0 < κ < 1/2 and b > 1. Assume that a single coefficient bounds the positive side of the integrated Mangoldt remainder by C₀ x^(1/2+κ) throughout arbitrarily late windows [Y,Y^b].

The cofinal bound excludes every zero with real part above 1/2+κ. The actual terminal defect therefore admits the bound K x^(κ−1/2)/log x for x≥exp(1).

For either sign, let Mw and Mq be the weighted and ordinary tail masses on [A,B], exp(1)≤A≤B, both normalized by 1/sqrt(t). The weighted tail carries the inverse logarithmic weight. Taking positive parts preserves the defect bound. Replacing log(t) in the denominator by log(A) gives the displayed integral comparison.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/RobinFixedExponentWindows.signed_mass_comparison_of_frequently_window_bound`
- Dependency: [D5/S3/Arith/Robin/Analytic/ZeroFreeStripMertensEnvelope](ZeroFreeStripMertensEnvelope.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent](../../../Weil/Mertens/IntegratedExplicit/SignedCompleteWindowExponent.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedTailWindowMass](../../../Weil/Mertens/WeightedTailWindowMass.md)
