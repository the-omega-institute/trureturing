# Tracial contractivity at the Wu endpoint

## Abstract

Tracial three-to-four contractivity of the signed two-mode Wu endpoint on positive semidefinite inputs.

**Theorem 1.1 (Strict contractivity for nonscalar inputs).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity_strict`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be a positive semidefinite two-mode matrix that is outside the ray of nonnegative scalar multiples of the identity. The cube of the fourth normalized trace moment of the signed endpoint applied to X is strictly less than the fourth power of the third normalized trace moment of X.

Join the mean-scaled identity to X by a segment of positive semidefinite matrices with constant normalized trace. The signed map preserves the identity and trace, so the image follows the corresponding segment. The ratio of the two moment powers starts at one. At each interior point its derivative has the opposite sign of the Euler expression bounded below by the quartic floor. The input variance there is the variance of X times the square of the segment parameter, so the floor is strictly positive. The mean value theorem gives the strict endpoint inequality.

**Theorem 1.2 (Contractivity on positive semidefinite inputs).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity` (`✓ std3`). ∎

*Citation.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

For every positive semidefinite two-mode matrix X, the cube of the fourth normalized trace moment of the signed endpoint applied to X is at most the fourth power of the third normalized trace moment of X.

This is the fixed tracial two-mode signed slice of Wu's Corollary 3.11 at beta = 0, p = 3 and r = 4, at the critical Gross-curve time. Remark 3.15 explicitly identifies the tracial case as proved.

The Lean proof recovers this known bound from strict contractivity off the nonnegative scalar ray and the scalar calculation on the ray.

**Theorem 1.3 (Equality on the nonnegative scalar ray).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive semidefinite two-mode matrix X the two moment powers are equal if and only if X is a nonnegative real scalar multiple of the identity. The endpoint fixes these matrices, including zero. The two powers for a scalar input both equal the twelfth power of its scalar.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity_eq_iff`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointQuarticContractivity.A1_quartic_contractivity_strict`
- Dependency: [D5/S3/Quantum/Semigroups/WuEndpointQuarticMajorization](WuEndpointQuarticMajorization.md)
