# Reverse geodesic CMI on a fixed marginal fiber

## Abstract

Faithful diagonal three-qubit states with all pair marginals fixed can produce an unbounded reverse geodesic CMI gap at vanishing trace distance.

**Theorem 1.1 (Classical relative entropy on faithful diagonals).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.geodesicRelativeEntropy_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.geodesicRelativeEntropy_diagonal` (`✓ std3`). ∎

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

For positive diagonal entries r and s, the modular eigenvalue at E_ij is r_i^(1−t) r_j^t / s_j. The reference vector contributes squared weight s_i at E_ii and vanishes on the other matrix units. This yields the classical relative entropy in equation (62).

**Definition 1.2 (Reverse geodesic conditional mutual information).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.reverseCMI`

*Formalization.* `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.reverseCMI` (`✓ std3`).

*Citation.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Equation (357) orders the joint divergence from the AB marginal tensored with the faithful C reference to the joint state. The subtracted divergence runs from the B marginal tensored with that reference to the BC marginal.

**Theorem 1.3 (All three pair marginals are fixed).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_fixed_marginals`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_fixed_marginals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Starting from the weights 0, 3/16, 1/8 and 1/16 indexed by Hamming weight, add x times the parity sign for 0 < x < 1/16. Every one-factor partial trace cancels the perturbation and leaves the same faithful diagonal pair marginal (3,5,5,3)/16.

**Theorem 1.4 (Exact trace distance).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_traceDistance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_traceDistance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

For the states with parameters x and x squared, the half trace norm of the difference is 4(x−x²).

**Theorem 1.5 (Divergence of the signed reverse gap).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_gap_tendsto_atTop`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_gap_tendsto_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

Subtract the value at x from the value at x squared. The reduced term cancels. The joint term at 000 is (3/16) times the C reference weight at zero times log(1/x). The other joint terms tend to zero.

**Theorem 1.6 (No modulus on the faithful diagonal fiber).**

Lean statement: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ángela Capel; Pablo Costa Rico (2026). *Geodesic Quantum f-Divergences*. URL: <https://arxiv.org/abs/2608.15833v1>.

*Commentary.*

The distance tends to zero from above and the signed gap tends to positive infinity, so no right-zero trace-distance modulus governs the faithful diagonal fiber. For the dimension-only question itself, equations (381)–(384) already give a binary obstruction with B trivial, and a fixed independent B can be adjoined by the tensor rule. The parity family above supplies a correlated three-qubit fiber with all three pair marginals fixed.

## References

- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_fixed_marginals`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_gap_tendsto_atTop`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.family_traceDistance`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.geodesicRelativeEntropy_diagonal`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.result`
- Truth anchor: `D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoReverseGeodesicCMI.reverseCMI`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation](../ChenKatoBrandaoTraceNormCMIRefutation.md)
- Dependency: [D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicModular](CapelCostaRicoGeodesicModular.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../PartialTraceMutualInformation.md)
