# Spectral majorization at the Wu endpoint

## Abstract

The ordered spectrum of the signed map is majorized by classical two-bit noise on the input spectrum.

Expanding a Hermitian input in terms of its three proper spectral prefix projections and the identity gives nonnegative coefficients for the projection terms. The projection bounds control each trace pairing. Applying this estimate to the ordered output eigenbasis yields the three spectral prefix inequalities, and trace preservation gives equality for the full sum.

**Theorem 1.1 (Proper spectral prefixes).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.A1_spectral_prefix`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.A1_spectral_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian two-mode matrix, the sum of the largest k output eigenvalues is at most the sum of the first k entries of the classical two-bit noise applied to the ordered input eigenvalues, for k equal to one, two or three.

**Theorem 1.2 (Spectral majorization).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.A1_spectral_majorization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.A1_spectral_majorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian two-mode input, the classical comparison vector is nonincreasing, it dominates all three proper output spectral prefixes, and its total sum equals the total output eigenvalue sum.

**Theorem 1.3 (Order of the classical comparison vector).**

Lean statement: `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.endpointClassical_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.endpointClassical_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The classical two-bit noise transform sends every nonincreasing four-vector to a nonincreasing four-vector.

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.A1_spectral_majorization`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.A1_spectral_prefix`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuEndpointPrefixMajorization.endpointClassical_antitone`
- Dependency: [D5/S3/Quantum/Semigroups/WuEndpointProjectionBounds](WuEndpointProjectionBounds.md)
