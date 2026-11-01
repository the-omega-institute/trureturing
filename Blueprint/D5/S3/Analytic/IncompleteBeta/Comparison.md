# Beta means and shape imbalance

## Abstract

Strict concentration comparison for symmetric beta means.

**Theorem 1.1 (Strict decrease with imbalance).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be a real continuous function on the closed unit interval, invariant under reflection about its midpoint, and strictly increasing on the interval from zero, excluded, to one half, included. For m positive, its normalized beta mean with shapes m+d and m-d is strictly decreasing for d from zero, included, to m, excluded. The normalization is the beta integral, equivalently the product of the two shape Gamma values divided by Gamma(2m).

Reflection folds both the moment and the normalizing integral onto the left half of the unit interval. There the density is twice [u(1-u)] to the power m-1 times cosh(d log((1-u)/u)). For two ordered nonnegative imbalances, the ratio of the larger tilt to the smaller tilt strictly decreases with u. With v=log((1-u)/u), the derivative in v of cosh(ev)/cosh(dv) has the sign of e sinh(ev)/cosh(ev) minus d sinh(dv)/cosh(dv). For positive imbalances, strict increase of r sinh(rv)/cosh(rv) in r supplies this sign. The zero imbalance follows from positivity of sinh at a positive argument. An iterated integral of the product of the differences in W and in the weighted densities is positive. Its algebraic expansion yields twice the difference between the cross-multiplied moments. The beta density is the fractional weight with parameters 1-m+d and 2m-1. Its integrability and Gamma-valued integral supply the endpoint control and normalization, while continuity of W ensures integrability of each moment.

**Theorem 1.2 (Strict comparison of weighted means).**

Lean statement: `D5/S3/Analytic/IncompleteBeta/Comparison.weighted_means_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/IncompleteBeta/Comparison.weighted_means_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On an interval (0,h) with h positive, let p and q be positive integrable weights, with integrable W-moments. If W strictly increases and q/p strictly decreases, then the q-weighted mean of W is strictly smaller than its p-weighted mean. The proof integrates the signed product of the differences in W and in the two weights, then cross-multiplies by their positive integrals. This same comparison also supplies the exponential remainder moment bounds in the general-parameter Mills module.

## References

- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Comparison.betaMean_strictAntiOn`
- Truth anchor: `D5/S3/Analytic/IncompleteBeta/Comparison.weighted_means_lt`
- Dependency: [D5/S3/Analytic/KilbasSaigo/Bounds](../KilbasSaigo/Bounds.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic](../../Entropy/RenyiCombining/ArimotoHyperbolic.md)
