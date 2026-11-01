# Null frontier of the Tribonacci Rauzy fractal

## Abstract

The frontier of the actual Tribonacci Rauzy fractal has planar Haar measure zero.

**Theorem 1.1 (The original Rauzy frontier has volume zero).**

Lean statement: `D5/S3/Geometry/Rauzy/TribonacciNullBoundary.rauzyFractal_frontier_volume_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Rauzy/TribonacciNullBoundary.rauzyFractal_frontier_volume_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex z belonging to the roots of the Tribonacci characteristic polynomial X^3 - X^2 - X - 1 and distinct from the real Tribonacci constant beta, volume(frontier(rauzyFractal z)) = 0. Here rauzyFractal z is the existing closure of finite exponent-zero admissible Boolean sums, with no three consecutive ones. Volume is the two-dimensional Haar measure on the complex plane. The three prefix branches are w mapped to z w, 1 + z^2 w, and 1 + z + z^3 w. The exact prefix cover, compactness and nonempty interior hold for this same set under these two root hypotheses. The root identities give z nonzero, norm(z) < 1 and beta norm(z)^2 = 1. The three branch area weights norm(z)^2, norm(z)^4 and norm(z)^6 are positive and sum to one by the reciprocal-power identity for beta. Multiplication by b scales planar Haar measure by norm(b)^2, from its real-linear determinant; translations preserve volume. All three branches are open and have common Lipschitz constant norm(z). The contracting-cover theorem constructs a whole interior cylinder and removes its positive weight from the frontier cover. Finite boundary mass then forces zero. Coverage, separation, tiling and a nullity premise are not additional hypotheses. The argument applies to both non-Perron roots.

## References

- Truth anchor: `D5/S3/Geometry/Rauzy/TribonacciNullBoundary.rauzyFractal_frontier_volume_zero`
- Dependency: [D5/S0/Tower/Tribonacci/Binet](../../../S0/Tower/Tribonacci/Binet.md)
- Dependency: [D5/S0/Tower/Tribonacci/RauzyFractal](../../../S0/Tower/Tribonacci/RauzyFractal.md)
- Dependency: [D5/S0/Tower/Tribonacci/Values](../../../S0/Tower/Tribonacci/Values.md)
- Dependency: [D5/S3/Geometry/Rauzy/TribonacciInterior](TribonacciInterior.md)
- Dependency: [D5/S3/Geometry/Rauzy/TribonacciRegularClosure](TribonacciRegularClosure.md)
- Dependency: [D5/S3/Topology/ContractingCoverNullBoundary](../../Topology/ContractingCoverNullBoundary.md)
