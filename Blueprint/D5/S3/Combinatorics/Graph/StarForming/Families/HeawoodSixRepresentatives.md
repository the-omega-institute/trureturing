# Six representatives of connected Heawood double covers

## Abstract

Every connected binary Heawood lift is represented by six explicit flag signings.

**Theorem 1.1 (Connected signings have one of six representatives).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodSixRepresentatives.exists_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodSixRepresentatives.exists_representative` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Each connected lift of the fixed Heawood flag graph, given by an arbitrary binary signing, is isomorphic to at least one of the six specified signings.

Connectivity makes the flag gain nonzero. Its trace is zero by incidence. The matrix classification puts the gain into one of six conjugacy forms. Each listed signing realizes its corresponding form by a sum of flag outer products. The transport of conjugate gains gives the graph isomorphism.

Pairwise nonisomorphism of the six graphs under arbitrary graph isomorphisms is a separate question. Source: Heawood double-cover gain. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L68-L108

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodSixRepresentatives.exists_representative`
- Dependency: [D5/S1/Eigenstructure/BinaryTraceZeroSimilarity](../../../../../S1/Eigenstructure/BinaryTraceZeroSimilarity.md)
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/Families/HeawoodMatrixAction](HeawoodMatrixAction.md)
