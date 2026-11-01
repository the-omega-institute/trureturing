# Neighborhood retraction and intersection

## Abstract

The variable neighborhood retraction and old-coordinate intersection bridge.

**Definition 1.1 (A variable-cutoff neighborhood retraction).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.neighborhoodRetraction`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.neighborhoodRetraction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

On O, apply the variable cutoff delta(x) to every coordinate and normalize. The coordinate sum exceeds three quarters, all support shrinks, and a minimizing b_M has its forbidden coordinates killed. The resulting continuous map lands in B. It fixes B pointwise because delta=0 there.

**Definition 1.2 (The actual neighborhood equivalence).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.neighborhoodEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.neighborhoodEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The variable-cutoff retraction and the inclusion of B in O are homotopy inverse. Straight interpolation is supported in the original independent face and stays in O by the b_M bound. The other composite is exactly the identity on B.

**Theorem 1.3 (Contractibility of the second open set).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.contractible_O`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.contractible_O` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

The constructed equivalence with the actual contractible apex star cluster makes O contractible. No homological vanishing assumption is supplied.

**Definition 1.4 (The actual open intersection).**

Lean statement: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.intersectionEquiv`

*Formalization.* `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.intersectionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Andrés Carnero Bravo (2025). *On independence complexes of graph products*. URL: <https://arxiv.org/abs/2505.06457v2>.

*Commentary.*

For every H less than or equal to G, the old epsilon cutoff and normalization map U intersect O to the actual old independence realization. Its denominator exceeds one quarter. Edges of H are excluded by a maximal independent set; edges retained from G minus H are excluded by the original gadget support. Inclusion on old coordinates is the inverse up to the two displayed straight homotopies.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.contractible_O`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.intersectionEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.neighborhoodEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteGraphSubgraphSuspensionRetraction.neighborhoodRetraction`
- Dependency: [D5/S3/Geometry/FiniteGraphSubgraphSuspensionConstruction](FiniteGraphSubgraphSuspensionConstruction.md)
