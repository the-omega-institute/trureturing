# CleanRoots

## Abstract

Auxiliary cut structure for full mutual-visibility reconfiguration.

**Theorem 1.1 (A clean root exists).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.exists_cleanRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.exists_cleanRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

A configuration cut smaller than the host order leaves a label whose singleton survives and for which no cut member has exactly that label outside the deleted-singleton labels.

**Definition 1.2 (Deleted singleton labels).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.deletedLabels`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.deletedLabels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

The finite host labels whose singleton configurations belong to the fixed cut.

**Definition 1.3 (One clean surviving root).**

Lean statement: `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.CleanRoot`

*Formalization.* `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.CleanRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Julián A. Fresán-Figueroa, Ilán A. Goldfeder, Aldo Lozano-Piña (2026). *Reconfiguration graphs of mutual-visibility sets*. DOI: [10.48550/arXiv.2610.24324](https://doi.org/10.48550/arXiv.2610.24324). URL: <https://arxiv.org/html/2610.24324v1>.

*Commentary.*

The label is outside the deleted singleton labels, and every member of the same cut has outside support different from that singleton label.

Deleted labels are those whose singleton configurations belong to one fixed cut. A clean root is a surviving label for which no cut configuration has that label as its entire support outside the deleted labels. If a cut has fewer members than the host has labels, at least one clean root exists: singleton cuts pay deleted labels, while disjoint one-label outside supports pay all other dirty labels. For a pair on deleted labels in a component separated from the clean root singleton, a feasible triple containing that root would give an uncut TAR path to the root. A host edge from a pair endpoint to the root would likewise give an uncut slide followed by deletion. Thus such triples are not visible and both endpoint-to-root host edges are absent. Mandatory root separation is excluded by a maximal pair-complete configuration and the sparse-slide degree bound. The minimum-pair degree count combines these exclusions with simultaneous inward payments to obtain the full separator conclusion.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.CleanRoot`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.deletedLabels`
- Truth anchor: `D5/S3/Combinatorics/Graph/MutualVisibility/CleanRoots.exists_cleanRoot`
- Dependency: [D5/S3/Combinatorics/Graph/MutualVisibility/Connectivity](Connectivity.md)
