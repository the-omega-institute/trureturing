# Categorical covers under finite-space subdivision

## Abstract

Categorical covers under finite-space subdivision

**Theorem 1.1 (Subdivision preserves finite homotopies of order maps).**

Lean statement: `D5/S3/Topology/SubdivisionCategoricalCover.subdivision_map_fence`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/SubdivisionCategoricalCover.subdivision_map_fence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Interpolate comparable maps by the cardinalities of principal lower sets. Along each interpolation step, the union of the two images of a chain remains a chain.

**Theorem 1.2 (Two categorical vertex subsets give two categorical opens after subdivision).**

Lean statement: `D5/S3/Topology/SubdivisionCategoricalCover.hasCategoricalCover_double_subdivision`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/SubdivisionCategoricalCover.hasCategoricalCover_double_subdivision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Intersect each chain meeting a selected set with that set, and then apply the subdivided contraction. The flags whose every chain meets one selected set form a lower set. The smallest chain of each flag supplies a vertex belonging to one of the two sets, so these lower sets cover.

## References

- Truth anchor: `D5/S3/Topology/SubdivisionCategoricalCover.hasCategoricalCover_double_subdivision`
- Truth anchor: `D5/S3/Topology/SubdivisionCategoricalCover.subdivision_map_fence`
- Dependency: [D5/S3/Topology/ConnectedCategoryGraft](ConnectedCategoryGraft.md)
- Dependency: [D5/S3/Topology/DescendingClosureContiguity](DescendingClosureContiguity.md)
