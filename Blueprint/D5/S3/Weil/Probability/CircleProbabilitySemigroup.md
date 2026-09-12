# CircleProbabilitySemigroup

## Abstract

Circle probability measures, the existing negative-power Fourier moments, and the existing Toeplitz matrices.

**Theorem 1.1 (Convolution multiplies the original Fourier moments).**

Lean statement: `D5/S3/Weil/Probability/CircleProbabilitySemigroup.circleMoment_mconv`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleProbabilitySemigroup.circleMoment_mconv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The convolution is the pushforward of the product of the actual Borel measures under circle multiplication. Fubini proves the moment identity.

**Theorem 1.2 (Construct the entire probability evolution).**

Lean statement: `D5/S3/Weil/Probability/CircleProbabilitySemigroup.circle_probability_semigroup_of_fourier`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleProbabilitySemigroup.circle_probability_semigroup_of_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All positive normalized matrices and multiplicative continuous coefficients construct one weakly continuous family, its identity law and its actual convolution law. Moment uniqueness gives family uniqueness.

**Theorem 1.3 (Exponential positivity is equivalent to a realized semigroup).**

Lean statement: `D5/S3/Weil/Probability/CircleProbabilitySemigroup.exponential_toeplitz_iff_probability_semigroup`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleProbabilitySemigroup.exponential_toeplitz_iff_probability_semigroup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponent has value zero at the identity. A probability semigroup with precisely the prescribed coefficients is constructed; neither Schoenberg nor an arithmetic Li criterion is assumed as a theorem.

**Theorem 1.4 (A represented exponential cannot have a negative exponent).**

Lean statement: `D5/S3/Weil/Probability/CircleProbabilitySemigroup.exponential_probability_forces_nonnegative`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Probability/CircleProbabilitySemigroup.exponential_probability_forces_nonnegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The modulus of every moment of a probability measure is at most one. The conclusion is necessary and does not assert that pointwise nonnegative exponents suffice for matrix positivity.

## References

- Truth anchor: `D5/S3/Weil/Probability/CircleProbabilitySemigroup.circleMoment_mconv`
- Truth anchor: `D5/S3/Weil/Probability/CircleProbabilitySemigroup.circle_probability_semigroup_of_fourier`
- Truth anchor: `D5/S3/Weil/Probability/CircleProbabilitySemigroup.exponential_probability_forces_nonnegative`
- Truth anchor: `D5/S3/Weil/Probability/CircleProbabilitySemigroup.exponential_toeplitz_iff_probability_semigroup`
- Dependency: [D5/S3/Weil/Probability/CircleHerglotzCompletion](CircleHerglotzCompletion.md)
