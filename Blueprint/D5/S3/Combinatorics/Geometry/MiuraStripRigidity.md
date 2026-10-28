# One-exit strip rigidity

## Abstract

A strip with no ambient maximum before its exit row is a vertical extrusion.

Chakshu Gupta, One construction for the Miura-ori flip-graph degree sequence, arXiv:2607.05567v3. The finite height suppliers are adapted from the accompanying CC BY 4.0 Lean source.

**Definition 1.1 (The actual rectangular restriction).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.stripMap`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.stripMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

The row offset embeds a full-width rectangular strip in the original height grid. Distances and edge increments refer to this same ambient array.

**Theorem 1.2 (Rigidity from one uphill exit).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.one_exit_strip_rigid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.one_exit_strip_rigid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

All maxima of the restricted array lie on its exit row: a restricted maximum elsewhere would also be an ambient maximum, because every existing outward edge above the strip is downhill. The finite maximum envelope and the row Lipschitz bound then force each column to have constant upward unit increment toward that row. A physical top boundary has no outward edge and satisfies the condition vacuously.

**Theorem 1.3 (An occupied internal strip forces a maximum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.occupied_internal_strip_has_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.occupied_internal_strip_has_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

In an internal strip whose outward top edges are downhill, an ambient extremum before the exit row forces an ambient maximum there. If no maximum existed, one-exit rigidity would make every vertex have a lower neighbour above, excluding a minimum as well.

**Theorem 1.4 (A slope reversal exposes an ambient maximum).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.first_reversal_has_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.first_reversal_has_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *One construction for the Miura-ori flip-graph degree sequence*. DOI: [10.48550/arXiv.2607.05567](https://doi.org/10.48550/arXiv.2607.05567). URL: <https://arxiv.org/abs/2607.05567v3>.

*Commentary.*

After a whole upward cut, suppose at least one edge of the next cut points downward. Choose a column of largest height among those reversing edges. Unit horizontal increments in both rows force both existing horizontal neighbours to be lower, even at an endpoint or when the chosen maximum has a nonadjacent tie. The preceding and succeeding vertical neighbours are lower too, so this is a full-grid maximum.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.first_reversal_has_maximum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.occupied_internal_strip_has_maximum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.one_exit_strip_rigid`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraStripRigidity.stripMap`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope](MiuraHeightEnvelope.md)
