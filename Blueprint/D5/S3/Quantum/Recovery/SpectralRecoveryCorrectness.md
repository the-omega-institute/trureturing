# SpectralRecoveryCorrectness

## Abstract

The computed spectral transpose recovery is exact whenever any represented Kraus left inverse exists. The proof derives observable intertwining from that inverse, then reuses cfc commutation and the computed support identity. Together with the finite Kraus criterion this closes the three-way equivalence in the finite representation.

**Theorem 1.1 (computed recovery of kraus left inverse).**

Lean statement: `D5/S3/Quantum/Recovery/SpectralRecoveryCorrectness.computed_recovery_of_kraus_left_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/SpectralRecoveryCorrectness.computed_recovery_of_kraus_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* H. Barnum and E. Knill (2002). *Reversing quantum dynamics with near-optimal quantum and classical fidelity*. DOI: [10.1063/1.1459754](https://doi.org/10.1063/1.1459754).

*Acknowledgement.* Ashwin Nayak and Pranab Sen (2007). *Invertible Quantum Operations and Perfect Encryption of Quantum States*. DOI: [10.26421/QIC7.1-2-6](https://doi.org/10.26421/QIC7.1-2-6).

*Acknowledgement.* Man-Duen Choi and Nathaniel Johnston and David W. Kribs (2009). *The multiplicative domain in quantum error correction*. DOI: [10.1088/1751-8113/42/24/245303](https://doi.org/10.1088/1751-8113/42/24/245303).

*Commentary.*

The computed spectral transpose recovery is exact whenever any represented Kraus left inverse exists. The proof derives observable intertwining from that inverse, then reuses cfc commutation and the computed support identity. Together with the finite Kraus criterion this closes the three-way equivalence in the finite representation.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/SpectralRecoveryCorrectness.computed_recovery_of_kraus_left_inverse`
- Dependency: [D5/S3/Quantum/Recovery/FiniteKrausReversibility](FiniteKrausReversibility.md)
- Dependency: [D5/S3/Quantum/Recovery/KrausLeftInverseNecessity](KrausLeftInverseNecessity.md)
- Dependency: [D5/S3/Quantum/Recovery/SpectralTransposeRecovery](SpectralTransposeRecovery.md)
