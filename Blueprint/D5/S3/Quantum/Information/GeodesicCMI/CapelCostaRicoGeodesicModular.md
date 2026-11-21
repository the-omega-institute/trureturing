# The geodesic modular operator

## Abstract

Geodesic relative entropy as a spectral quadratic form in matrix-unit coordinates.

**Definition 1.1 (Action on Hilbert–Schmidt matrices).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicAction`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicAction` (`✓ std3`).

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Equation (52) left-multiplies by the first matrix to the power 1−t and right-multiplies by its t-th power conjugated by the inverse square root of the second matrix.

**Definition 1.2 (Matrix of the modular operator).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicModular`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicModular` (`✓ std3`).

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

The column indexed by a matrix unit contains the coordinates of its image under the action in equation (52).

**Definition 1.3 (Coordinates of the reference square root).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.weightedVector`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.weightedVector` (`✓ std3`).

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

The vector lists the entries of the square root of the second matrix. It represents the Hilbert–Schmidt vector in equation (59).

**Definition 1.4 (Geodesic relative entropy).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicRelativeEntropy`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicRelativeEntropy` (`✓ std3`).

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Equations (59) and (63) pair the result of applying the spectral function z ↦ z log z of the modular matrix to the reference vector with that same vector. Lean takes the real part of the complex quadratic form.

**Theorem 1.5 (Kronecker representation).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicModular_eq_kronecker`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicModular_eq_kronecker` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

In the chosen ordering of matrix units, the right multiplication factor is transposed in the Kronecker representation. The left factor is the (1−t)-th power of the first matrix.

## References

- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicAction`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicModular`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicModular_eq_kronecker`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.geodesicRelativeEntropy`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular.weightedVector`
