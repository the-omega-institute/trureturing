# Interpolation of the literal seven-site cofactor quotients

## Abstract

Interpolation of the literal seven-site cofactor quotients

**Theorem 1.1 (Identification of the affine quotient).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueComparison.identify_line_quotient`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueComparison.identify_line_quotient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For deletion of row zero or one modulo 1009, take an exact quotient of the literal cofactor by the mixed-trace coordinate. Assume the stated value and derivative comparisons at the seven entry sample points and the tabulated determinant identities at the forty-seven quotient nodes. Then the quotient restricted to the specified affine line equals the tabulated polynomial. The mixed-trace coordinate is nonzero at each quotient node, so cancellation and the degree bound permit interpolation.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueComparison.identify_line_quotient`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueBezout](SevenSiteResidueBezout.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteResidueRows](SevenSiteResidueRows.md)
