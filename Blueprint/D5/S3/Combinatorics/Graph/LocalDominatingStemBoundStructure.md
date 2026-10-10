# Deleting a stem and its leaves

## Abstract

The residual graph has no isolated vertices when the original graph has none.

**Definition 1.1 (Residual vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining`

*Formalization.* `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove the specified vertex and all its leaf neighbours.

**Theorem 1.2 (A retained neighbour).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining_neighbor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining_neighbor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A residual vertex has a neighbour other than the removed stem; that neighbour cannot be one of the removed leaves.

**Theorem 1.3 (Residual absence of isolates).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.residualGraph_no_isolates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.residualGraph_no_isolates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each vertex of the induced residual graph has an adjacent residual vertex.

**Theorem 1.4 (Order decomposition).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The graph order is the residual order plus the number of removed leaves plus one.

**Definition 1.5 (Partial residual domination).**

Lean statement: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.partialDomSets`

*Formalization.* `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.partialDomSets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Require internal domination only for residual vertices not adjacent to the removed stem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.partialDomSets`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.remaining_neighbor`
- Truth anchor: `D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure.residualGraph_no_isolates`
- Dependency: [D5/S3/Combinatorics/Graph/DominatingSetAverage](DominatingSetAverage.md)
