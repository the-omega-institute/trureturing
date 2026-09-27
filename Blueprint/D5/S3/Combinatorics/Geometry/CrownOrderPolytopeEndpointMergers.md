# Merging selected blocks into endpoints

## Abstract

Selected odd blocks yield connected compatible augmented partitions.

This is the source-directed construction in Proposition 3.3(i): lower-majority selected blocks join the bottom, upper-majority selected blocks join the top.

**Theorem 1.1 (Endpoint merging and quotient cardinality).**

Lean statement: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointMergers.twoSidedMergeCCP_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointMergers.twoSidedMergeCCP_card` (`✓ std3`). ∎

*Citation.* Teemu Lundström and Leonardo Saud Maia Leite (2025). *Order polytopes of crown posets*. DOI: [10.48550/arXiv.2504.05123](https://doi.org/10.48550/arXiv.2504.05123). URL: <https://arxiv.org/abs/2504.05123v3>.

*Commentary.*

For n at least two, a connected compatible cycle partition and a selection of its odd blocks determine disjoint lower and upper selections covering the original selection. Merging these selections into the bottom and top endpoints yields an actual quotient with cardinality equal to the original quotient cardinality minus the selected cardinality plus two. Odd-block geometry supplies the required orientation and compatibility.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointMergers.twoSidedMergeCCP_card`
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeOddBlocks](CrownOrderPolytopeOddBlocks.md)
