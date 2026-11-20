# Zero clusters at the unattained zeta zero abscissa

## Abstract

Finite critical Möbius energy excludes narrow selected clusters at the unattained zeta zero abscissa.

**Theorem 1.1 (Exclusion of narrow high zero clusters).**

$$\sum_{z}\,D(z)\neq q$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaPntBounds/MobiusBoundaryClusterExclusion.no_selectedZeroCluster_atHighOrdinate_of_unattainedZeroAbscissa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Θ < 1 be the unattained supremum of the real parts of nontrivial zeta zeros. For the finite sum S(x) of μ(n)/n over positive integers n ≤ x, assume that (S(x) − S(2x))² x^(1−2Θ) is integrable over x > 1. Fix real p > 0 and a positive integer q with p(2q − 1) > 2.

There are positive R and T such that for every |t| ≥ T and every 0 < r ≤ |t|^(−p), take any nonnegative divisor D dominated by the zeta divisor on the closed disk of radius R centered at Θ + it. If its support lies within the closed disk of radius r about the same center and strictly to the left of Θ, the sum of its selected multiplicities is different from q.

A nontrivial zero with real part at least one half, together with unattainment, gives Θ > 1/2. The supremum property and zeta nonvanishing for real part at least one give a zero-free right half-plane away from the pole, and unattainment excludes line zeros. Three-circles interpolation and the logarithm estimates from ZetaReciprocalSubpolynomial give a fixed-disk bound of order |t|^ε. The analyticity and finite-order lemmas in StatementSeam justify factoring the selected divisor. This gives a lower bound on the weighted reciprocal-square mass on an interval of length 2r. The energy bound then forces 2 ≤ C |t|^(2+2ε) r^(2q−1) for a constant C, which fails at large |t| when 2+2ε < p(2q−1).

## References

- Truth anchor: `D5/S3/Weil/ZetaPntBounds/MobiusBoundaryClusterExclusion.no_selectedZeroCluster_atHighOrdinate_of_unattainedZeroAbscissa`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/KappaGap](../../Arith/Robin/ForwardKernel/KappaGap.md)
- Dependency: [D5/S3/Weil/Mertens/MobiusDyadicEnergy](../Mertens/MobiusDyadicEnergy.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusDyadicBoundary](MobiusDyadicBoundary.md)
- Dependency: [D5/S3/Weil/ZetaPntBounds/MobiusPartialSumL2Divergence](MobiusPartialSumL2Divergence.md)
