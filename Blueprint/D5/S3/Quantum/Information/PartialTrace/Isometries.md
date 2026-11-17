# Partial trace through product isometries

## Abstract

Partial trace through product isometries.

**Theorem 1.1 (Partial trace through product isometries).**

Lean statement: `D5/S3/Quantum/Information/PartialTrace/Isometries.partialTrace_isometries`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PartialTrace/Isometries.partialTrace_isometries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite complex matrices v and w, if w adjoint times w is the identity, tracing the second factor of (v tensor w) z (v tensor w) adjoint gives v times the partial trace of z times v adjoint. The first matrix need not be an isometry. The proof contracts the w coefficients using column orthogonality. The declaration retains its AnticoherenceSpinCovariance namespace.

## References

- Truth anchor: `D5/S3/Quantum/Information/PartialTrace/Isometries.partialTrace_isometries`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../PartialTraceMutualInformation.md)
