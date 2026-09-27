# Boundary cuts of a cycle partition

## Abstract

Connected cycle partitions are encoded by their boundary cuts.

The cut-set construction makes explicit the partition/edge-deletion correspondence used in the proof of source Lemma 3.5. No new enumerative formula is claimed here.

**Theorem 1.1 (No boundary cuts exactly for the one-block partition).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts.cycleBoundaryCuts_eq_empty_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts.cycleBoundaryCuts_eq_empty_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For a nonzero cycle size at least three, a connected partition has no boundary cuts if and only if every two vertices are equivalent.

**Definition 1.2 (The boundary-cut equivalence).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts.connectedCyclePartitionCutsEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts.connectedCyclePartitionCutsEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For a nonzero cycle size at least three, connected partitions with at least two boundary cuts are explicitly equivalent to cut sets with at least two elements. The inverse uses the connected components after deleting the selected successor edges. The one-block case is excluded from this equivalence and handled separately by the empty-boundary characterization.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts.connectedCyclePartitionCutsEquiv`
- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts.cycleBoundaryCuts_eq_empty_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration](CrownOrderPolytopeEnumeration.md)
