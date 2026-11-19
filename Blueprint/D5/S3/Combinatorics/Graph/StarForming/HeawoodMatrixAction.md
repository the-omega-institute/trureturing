# Coordinate transport of Heawood double covers

## Abstract

Conjugating the Fano flag gain transports the actual two-sheet graph.

**Theorem 1.1 (Conjugate gains give isomorphic double covers).**

Lean statement: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMatrixAction.isomorphic_of_phi_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/StarForming/HeawoodMatrixAction.isomorphic_of_phi_conjugate` (`✓ std3`). ∎

*Citation.* The Omega Institute repository contributors (2026). *Star-forming composition, certificate and cover results*. URL: <https://github.com/the-omega-institute/subquorum-colorings/tree/48728b42d39ab3de5de251c61da5a404ec418a69>.

*Commentary.*

Let s and t be signings of the twenty-one flags of the binary Fano plane. If the linear gain of t equals g times the gain of s times the inverse of g for an invertible binary three-by-three matrix g, the two-sheet graphs of s and t are isomorphic.

The matrix acts on nonzero point columns and its inverse acts on nonzero line rows. Their pairing is invariant, so the resulting permutation acts on flags. Under the same permutation, each point-line outer product is conjugated by g and the corresponding signing weight travels with the flag. The graph relabeling keeps the sheet coordinate. The equal-gain switching theorem transports the resulting signing to t.

Source: Heawood double-cover gain, linear conjugacy. https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/HEAWOOD_DOUBLE_COVER_GAIN.md#L26-L108

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/StarForming/HeawoodMatrixAction.isomorphic_of_phi_conjugate`
- Dependency: [D5/S3/Combinatorics/Graph/StarForming/HeawoodLift](HeawoodLift.md)
