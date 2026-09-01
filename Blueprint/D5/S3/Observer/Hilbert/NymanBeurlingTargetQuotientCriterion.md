# Nyman-Beurling Target Quotient Criterion

## Abstract

The Nyman-Beurling membership criterion is equivalent to quotient, residual-projection, and finite-stage distance criteria in an abstract Hilbert space.

**Theorem 1.1 (Five equivalent Nyman-Beurling target criteria).**

Lean statement: `D5/S3/Observer/Hilbert/NymanBeurlingTargetQuotientCriterion.nyman_beurling_target_quotient_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanBeurlingTargetQuotientCriterion.nyman_beurling_target_quotient_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The analytic Nyman-Beurling theorem is an explicit hypothesis connecting the abstract proposition RH to membership in the closed cumulative space; the formalization does not define RH by that membership.

The remaining equivalences are proved from Hilbert-space geometry: the quotient class vanishes exactly on the subspace, projection onto its orthogonal complement vanishes exactly on the closed subspace, and distances to a monotone tower tend to zero exactly on its closed union.

Constant coordinate-line towers in the real Euclidean plane witness both the simultaneously true and the simultaneously false cases.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/NymanBeurlingTargetQuotientCriterion.nyman_beurling_target_quotient_criterion`
- Dependency: [D5/S3/Quantum/Algebra/DoubleOrthogonalClosure](../../Quantum/Algebra/DoubleOrthogonalClosure.md)
- Dependency: [D5/S3/Quantum/Completion/BoundedInverseLimitReconstruction](../../Quantum/Completion/BoundedInverseLimitReconstruction.md)
