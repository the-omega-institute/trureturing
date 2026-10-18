# The sharp spectral moment inequality

## Abstract

The real-order characteristic-root moment bound and its strict-order rigidity.

**Theorem 1.1 (The bound and necessary equality condition).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurMomentInequality.spectral_bound_and_rigidity`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurMomentInequality.spectral_bound_and_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>0, nonzero complex b_j and every real p≥1, the sum of norm(mu)^p over characteristic roots of diag(b)(I+J), with multiplicity, is at most ((n+1)^p+n−1)/n times sum_j norm(b_j)^p. For p>1, equality implies b_i=b_j for every i,j. The endpoint uses the unitary rank-one trace bound; strict orders use one fixed Schur basis, scalar three-lines interpolation and propagation of equality to all right boundary phases.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurMomentInequality.spectral_bound_and_rigidity`
- Dependency: [D5/S3/Zeros/CriticalPoints/SchurMomentNormalization](SchurMomentNormalization.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/SchurStripBoundary](SchurStripBoundary.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/SchurStripCenter](SchurStripCenter.md)
