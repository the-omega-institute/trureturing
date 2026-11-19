# The four-site periodic sextic

## Abstract

The four-site periodic matrix product state sextic and its first-order boundary vanishing

**Definition 1.1 (The necklace polynomial).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The six inputs are the amplitudes of 0000, 1000, 1100, 1010, 1110 and 1111. The polynomial is written in powers of the singlet coordinate d minus c.

**Theorem 1.2 (Vanishing on the actual tensor image).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The two-by-two trace recurrence writes the six amplitudes in terms of two traces, two determinants and one mixed trace. Substitution into the Critch–Morton sextic gives zero for every pair of complex bond matrices.

**Theorem 1.3 (First-order vanishing at the rank-one triplet boundary).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_rank_one_triplet`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_rank_one_triplet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

On the triplet rank-one parametrization, the sextic vanishes for arbitrary first-order variations in the six coordinates.

**Theorem 1.4 (First-order vanishing at the zero-singlet boundary).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_singular_triplet_zero_singlet`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_singular_triplet_zero_singlet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

When the singlet vanishes and the triplet is singular, the sextic has zero value and zero first derivative. The negative square and triplet determinant formula yields both vanishings.

**Theorem 1.5 (Equal nonzero marginal fixes the norm of the phase).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.phase_of_proportional_flattening`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.phase_of_proportional_flattening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For proportional four-site flattenings with a common nonzero raw two-site marginal, the proportionality scalar has absolute value one and relates every full amplitude.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.phase_of_proportional_flattening`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_actual`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_rank_one_triplet`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSFourSiteSextic.sextic_singular_triplet_zero_singlet`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity](PeriodicMPSTwoSiteAmbiguity.md)
