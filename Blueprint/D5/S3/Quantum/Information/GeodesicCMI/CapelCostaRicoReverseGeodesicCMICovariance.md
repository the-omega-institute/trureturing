# Reverse geodesic CMI for a faithful qubit reference

## Abstract

A change of basis transports the reverse counterexample to any faithful qubit reference.

**Theorem 1.1 (Unitary covariance of geodesic relative entropy).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.geodesicRelativeEntropy_conjugation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.geodesicRelativeEntropy_conjugation` (`✓ std3`). ∎

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Simultaneous conjugation of the two matrices induces a unitary conjugation on matrix-unit coordinates and transports the square-root vector. This is the spectral-form realization of the covariance in Proposition 4.3.

**Theorem 1.2 (Covariance of the reverse deficit).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.reverseCMI_conjugation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.reverseCMI_conjugation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

The local unitary on C acts on the reference as well as on the state. The actual partial traces conjugate with the retained local unitaries, so both divergences in equation (357) are preserved.

**Theorem 1.3 (No modulus on one transported fiber).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.native_result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.native_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Diagonalize the faithful qubit reference and transport the faithful parity witnesses back to the original coordinates. The trace distance and both divergences are preserved. The AB marginal is unchanged by the C rotation, and the rotated AC and BC marginals stay fixed throughout the fiber.

**Theorem 1.4 (No reverse modulus for faithful three-qubit states).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.noDimensionOnlyModulus`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.noDimensionOnlyModulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

A modulus on all faithful three-qubit states would restrict to the transported fiber, even if it were allowed to depend on the parameter and the faithful reference. This applies throughout the preprint's parameter interval. The binary calculation in equation (384) supplies the earlier implication for the dimension-only question.

## References

- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.geodesicRelativeEntropy_conjugation`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.native_result`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.noDimensionOnlyModulus`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMICovariance.reverseCMI_conjugation`
- Dependency: [D5/S3/Quantum/Entanglement/ConicalDesignConcurrenceComparability](../../Entanglement/ConicalDesignConcurrenceComparability.md)
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI](CapelCostaRicoReverseGeodesicCMI.md)
- Dependency: [D5/S3/Quantum/Information/PartialTrace/Isometries](../PartialTrace/Isometries.md)
