# Compact Separated Real Continuation

## Abstract

A continuous compact connected family of real polynomials preserves real roots when distinct roots stay uniformly separated.

**Theorem 1.1 (Real roots persist through a separated family).**

Lean statement: `D5/S3/Zeros/Jensen/CompactSeparatedRealContinuation.compact_separated_real_family`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/CompactSeparatedRealContinuation.compact_separated_real_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a compact preconnected topological space, let q be any natural number, and let P assign a complex polynomial to every point of A. Assume every P(x) is monic and has natural degree q, every coefficient is a continuous function of x, and every coefficient has imaginary part zero. Assume a real d greater than zero bounds below the distance between any two distinct complex roots of the same P(x), uniformly for x in A. If every root of P(x0) has imaginary part zero for some x0 in A, then every root of every P(x) has imaginary part zero.

The conclusion quantifies over all roots, with no choice of root labels or differentiable paths. The separation premise concerns distinct root values and does not separately assume squarefreeness. For q equal to zero, monicity forces P(x)=1, so the conclusion is vacuous. The point x0 supplies nonemptiness of the parameter space. No external uniform root bound is required.

For positive degree, the finite coefficient sum is continuous and attains a maximum on A. The polynomial Cauchy bound therefore supplies a uniform root bound. Real coefficients pair each nonreal root with its conjugate, so separation forces the magnitude of its imaginary part to be at least d/2. Mathlib's quantitative root approximation from coefficient closeness then makes the set of parameters with all real roots both open and closed. It contains x0, and preconnectedness makes it the whole parameter space.

This is a classical polynomial continuity argument, formalized as a reusable implication. In the Appell route, the intended parameter space is the closed real interval [0,1], with a Hermite polynomial at zero and the actual source polynomial at one. Coefficient continuity, coefficient reality, fixed degree, the Hermite endpoint, and uniform distinct-root separation for that exact family must all be proved separately before this theorem applies. It proves no RH, global Robin inequality, node-sign law or source transmission estimate, and makes no claim of literature originality.

**Theorem 1.2 (The existing Cauchy root-bound helper is reusable).**

Lean statement: `D5/S3/Zeros/Jensen/CompactSeparatedRealContinuation.monic_root_bound_by_coefficient_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/CompactSeparatedRealContinuation.monic_root_bound_by_coefficient_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a monic complex polynomial P and a root z, the norm of z is at most one plus the sum of the norms of coefficients below its natural degree. Mathlib's Cauchy root bound is at most this coefficient sum because the maximum lower-coefficient norm is bounded by their sum. This previously private helper is exposed with the same statement and proof for actual use by the root-projection properness theorem. Its public visibility introduces no new mathematical content.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/CompactSeparatedRealContinuation.compact_separated_real_family`
- Truth anchor: `D5/S3/Zeros/Jensen/CompactSeparatedRealContinuation.monic_root_bound_by_coefficient_sum`
