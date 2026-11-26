# Actual canonical Li curvature Toeplitz criterion

## Abstract

The normalized canonical Li curvature is given by the actual positive-ordinate zero pairs under right-half-plane nonvanishing, yielding a Toeplitz criterion for the Riemann hypothesis.

**Theorem 1.1 (Positive semidefiniteness of the actual curvature).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiCurvatureForward.canonical_curvature_forward_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/ActualCanonicalLiCurvatureForward.canonical_curvature_forward_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N, if N is zero or the completed xi function has no zeros in the open half-plane with real part greater than one half, the order-N Toeplitz matrix of the derivative-defined canonical Li curvature is positive semidefinite. The order-zero matrix has the single entry one.

On the critical line, write a for the Cayley ratio of an actual zero and C_n for its pair contribution in degree n. For every natural n, the difference C_(n+2) - 2 C_(n+1) + C_n is C_1 times the sum of the powers of a and its conjugate of degree n+1. Dividing by twice the first canonical Li coefficient assigns a positive mass to each member of every positive-ordinate pair. The masses over both members of all pairs sum to one by the coefficient identity at degree one.

At each order N, the weighted vectors of powers from zero through N for each pair give two rank-one Gram matrices per pair. Unit modulus identifies their entries with the moments at integer index differences. The absolute summability of the actual pair coefficients gives entrywise convergence of the finite Gram sums to the canonical Toeplitz matrix, which belongs to the closed positive semidefinite cone.

**Theorem 1.2 (Riemann hypothesis and all curvature Toeplitz orders).**

Lean statement: `D5/S3/Weil/Probability/ActualCanonicalLiCurvatureForward.rh_iff_canonical_curvature_posSemidef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/ActualCanonicalLiCurvatureForward.rh_iff_canonical_curvature_posSemidef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Riemann hypothesis holds exactly when the Toeplitz matrix of the actual normalized canonical Li curvature is positive semidefinite at every natural order. The forward direction applies the Gram construction using right-half-plane nonvanishing. The reverse direction uses the two-point compression of the actual curvature Toeplitz matrices and the canonical Li growth criterion.

## References

- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiCurvatureForward.canonical_curvature_forward_posSemidef`
- Truth anchor: `D5/S3/Weil/Probability/ActualCanonicalLiCurvatureForward.rh_iff_canonical_curvature_posSemidef`
- Dependency: [D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent](ActualCanonicalLiForwardPairedResolvent.md)
- Dependency: [D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree](CanonicalLiCurvatureZeroFree.md)
