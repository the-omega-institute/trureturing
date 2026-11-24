# Local-unitary covariance of the actual anchor form

## Abstract

Local-unitary covariance of the actual anchor form.

**Theorem 1.1 (Resolvent derivative covariance).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.logDeriv_inBasis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.logDeriv_inBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unitary conjugation commutes with each shifted inverse and hence with the integrated log resolvent derivative.

**Theorem 1.2 (Preservation of the tangent conditions).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.marginalFree_inBasis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.marginalFree_inBasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local conjugation preserves Hermiticity. Each partial trace transforms by conjugation on its remaining subsystem and therefore stays zero.

**Theorem 1.3 (Transfer of the entire quadratic).**

Lean statement: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.anchorQuadraticIn_normalForm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.anchorQuadraticIn_normalForm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local conjugation transports the product density and tangent. Relabeling and rephasing outcomes preserve the two Fisher sums, and trace invariance preserves the BKM term.

## References

- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.anchorQuadraticIn_normalForm`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.logDeriv_inBasis`
- Truth anchor: `D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport.marginalFree_inBasis`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormHadamard](AnchorMUBNormalFormHadamard.md)
- Dependency: [D5/S3/Quantum/Recovery/BKMSpectralVariance](../../Recovery/BKMSpectralVariance.md)
