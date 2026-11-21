# Faithful pairs with matching two-body marginals

## Abstract

Faithful three-qubit witness pairs share their AB, AC and BC marginals within each pair.

**Definition 1.1 (Regularized three-qubit witness).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.RMatrix`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.RMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Acknowledgement.* Andris Ambainis; Michele Mosca; Alain Tapp; Ronald de Wolf (2000). *Private Quantum Channels*. DOI: [10.1109/SFCS.2000.892142](https://doi.org/10.1109/SFCS.2000.892142).

*Commentary.*

The reference S_u is (I + (1−2u) Z_A Z_B)/8 with identity on C. The witness adds (1−η) √(u(1−u)) X_A Z_B Z_C/4. The balanced real-state masking by I and Y on a qubit is the antecedent for the cancellation on AC.

**Theorem 1.2 (Faithfulness under regularization).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.RMatrix_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.RMatrix_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

The unsmoothed matrix is positive semidefinite and S_u is positive definite for 0 < u < 1/2. Mixing in a weight 0 < η < 1 of S_u makes the witness positive definite.

**Theorem 1.3 (Equality of the three two-body marginals).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.pair_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.pair_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Acknowledgement.* Andris Ambainis; Michele Mosca; Alain Tapp; Ronald de Wolf (2000). *Private Quantum Channels*. DOI: [10.1109/SFCS.2000.892142](https://doi.org/10.1109/SFCS.2000.892142).

*Commentary.*

Every one-factor partial trace kills X_A Z_B Z_C. Both AC and BC are I/4. The common AB marginal is diagonal with entries (1−u,u,u,1−u)/2.

**Theorem 1.4 (Exact distance between the faithful states).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.traceDistance_R_S`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.traceDistance_R_S` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

The trace distance is (1−η) √(u(1−u)). The Pauli product in the difference is a self-adjoint involution, so the absolute value has a constant eigenvalue on the eight-dimensional space.

## References

- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.RMatrix`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.RMatrix_posDef`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.pair_marginals`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity.traceDistance_R_S`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Information/Pauli/PauliMatrix](../Pauli/PauliMatrix.md)
