# Exact Fourier signs

## Abstract

All-real sign identities for Fourier modes and short spectral gaps.

**Theorem 1.1 (Mode signs from forced roots).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.modeValue_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.modeValue_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m,j with 1 at most j at most m, and every real exponent r, the sign of the Fourier mode lambda_j(r) equals the sign of the product of r-2s over 0 at most s less than j. The positive cosine bases give strictly decreasing logarithmic exponents. The coefficient variation count and the j prescribed even roots exhaust the exponential Descartes bound; the constant coefficient is positive.

**Theorem 1.2 (Signs of short spectral gaps).**

Lean statement: `D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.modeValue_gap_sign`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.modeValue_gap_sign` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural j at least one and d equal to one or two with j+d at most m, and every real r, lambda_j(r)-lambda_(j+d)(r) has the sign of the same product. The sine-product coefficient list has j variations even when intermediate coefficients vanish. Its first coefficient is strictly positive. The common even roots and the exact exponential-sum sign theorem give the identity, with no restriction on primality of the odd order.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.modeValue_gap_sign`
- Truth anchor: `D5/S3/Quantum/Matrix/JainAbsCosine/GapSigns.modeValue_sign`
- Dependency: [D5/S3/Analytic/ExponentialSum/DescartesRule](../../../Analytic/ExponentialSum/DescartesRule.md)
- Dependency: [D5/S3/Quantum/Matrix/JainAbsCosine/ForcedZeros](ForcedZeros.md)
- Dependency: [D5/S3/Quantum/Matrix/JainAbsCosine/TrigSignChanges](TrigSignChanges.md)
