# Pole exclusion from one-sided upper windows

## Abstract

One-sided long windows exclude poles of an actual signed Laplace transform.

This repo-derived theorem uses an abstract signed density, an actual analytic continuation and locally discrete simple poles. It separates the window condition from the exponent range and requires no theta less than one. The explicit coefficient estimate has nonnegative constants and no exponential loss.

**Theorem 1.1 (Geometric coefficient bounds from the actual windows).**

Lean statement: `D5/S3/Analytic/Laplace/LongWindowPoleExclusion.long_window_pole_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/LongWindowPoleExclusion.long_window_pole_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

A pole to the right of the window exponent gives a positive principal scale with a strictly larger remainder scale. On arbitrarily late windows, the same actual derivative order produces the geometric lower and upper estimates. The constants depend on the density, continuation, and pole, and the upper constant is independent of the window cutoff. The constants sigma is fixed before the cutoff, with sigma greater than two and theta; E equals sigma minus theta. The positive scales obey d less than e less than E; B and K are nonnegative. At arbitrarily large U at least one, the same integer k=floor(sigma*((2+delta)/2)*U), at least U, satisfies c/d^k at most B/e^k plus K/E^k.

**Theorem 1.2 (Long windows exclude every pole to the right of their exponent).**

Lean statement: `D5/S3/Analytic/Laplace/LongWindowPoleExclusion.long_window_pole_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/LongWindowPoleExclusion.long_window_pole_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Levent Alpöge (2026). *Riemann hypothesis formalization in Lean*. URL: <https://github.com/the-omega-institute/riemann-hypothesis>.

*Commentary.*

Let a measurable real density have an absolute exponential bound. Its actual Laplace integral agrees on a right half-plane with a continuation analytic on the positive half-plane away from a locally discrete set of simple poles. Assume these poles have real part at most the value one, have nonzero residues, and have positive real residues when the poles themselves are real.

If upper bounds with exponent theta hold on arbitrarily late intervals from U to a fixed multiple of U, then every pole has real part at most theta. The interval multiple may be any fixed number larger than one, and theta may be any nonnegative number.

At a suitable real center, either a pole-free disk controls the real signed moments, or a real nearest pole has a positive principal coefficient. In the former case a small vertical displacement isolates a single pole. Cauchy bounds control its analytic remainder. Actual moments at one common high order are bounded using the upper window and the absolute growth bound outside it. The two different geometric rates then contradict a pole to the right of theta.

The analytic continuation and residue hypotheses must be verified for the function under consideration. This theorem does not infer them from the window bound.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/LongWindowPoleExclusion.long_window_pole_estimate`
- Truth anchor: `D5/S3/Analytic/Laplace/LongWindowPoleExclusion.long_window_pole_exclusion`
- Dependency: [D5/S3/Analytic/Isolation/VerticalNearestPole](../Isolation/VerticalNearestPole.md)
- Dependency: [D5/S3/Analytic/Laplace/LongWindowBounds](LongWindowBounds.md)
- Dependency: [D5/S3/Analytic/Laplace/SignedWindowMoments](SignedWindowMoments.md)
- Dependency: [D5/S3/Weil/Mertens/Cryptids/WeightedStieltjes/Residues](../../Weil/Mertens/Cryptids/WeightedStieltjes/Residues.md)
