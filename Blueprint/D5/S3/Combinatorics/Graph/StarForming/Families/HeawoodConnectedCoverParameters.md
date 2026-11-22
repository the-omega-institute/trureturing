# The complete binary-lift parameter dichotomy

## Abstract

The complete binary-lift parameter dichotomy

The six similarity types N1, N2, S, J, C and K reduce to the same matching construction. Their ordered bases have Fano labels (2, 4, 1) for N1, (4, 1, 2) for N2 and (1, 4, 2) for the other four. The pairs (u, v) in these bases are (0, 0), (0, 0), (0, 1), (0, 1), (0, 0) and (1, 0). Every pair enables an additional line, so the matching gives beta at least fifteen. The star-forming maximum is sixteen for every signing and bounds beta above. Disconnected signings have beta fourteen. The bound leaves the exact values for N1, N2, C and K open here.

**Theorem 1.1 (Dissociation bounds for connected lifts).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.connected_beta`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.connected_beta` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Every connected binary lift of the Heawood graph has beta between fifteen and sixteen.

**Theorem 1.2 (The complete dichotomy).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.parameters`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.parameters` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Every binary lift of the Heawood graph has SF equal to sixteen. Its beta is fourteen exactly when the lift is disconnected. A connected lift has beta fifteen or sixteen and gap at most one.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.connected_beta`
- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodConnectedCoverParameters.parameters`
- Dependency: [D5/S1/Eigenstructure/BinaryTraceZeroSimilarity](../../../../../S1/Eigenstructure/BinaryTraceZeroSimilarity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatching](HeawoodMatching.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodCoverParameters](../HeawoodCoverParameters.md)
