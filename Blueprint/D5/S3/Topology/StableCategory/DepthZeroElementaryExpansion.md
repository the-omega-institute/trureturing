# Categorical covers across an elementary expansion

## Abstract

Categorical covers across an elementary expansion

**Theorem 1.1 (Extension of a two-piece cover).**

Lean statement: `D5/S3/Topology/StableCategory/DepthZeroElementaryExpansion.two_lower_sets_after_elementary_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/DepthZeroElementaryExpansion.two_lower_sets_after_elementary_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Suppose the retained complex of an elementary collapse has a categorical cover by two subcomplexes and the expanded complex is connected. After two ordinary barycentric subdivisions, the face poset of the expanded complex has a categorical lower cover of size two.

In the mixed case, collect the vertices omitted by the attaching facets that belong to the second old piece. The resulting face lies in the first piece and in every old attaching face exclusive to that piece. It gives a single contiguity comparison for both new face vertices. For a monochromatic attachment, the opposite piece has a separate new edge that contracts and then moves along an ambient path.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/DepthZeroElementaryExpansion.two_lower_sets_after_elementary_expansion`
- Dependency: [D5/S3/Geometry/FiniteElementaryCollapse](../../Geometry/FiniteElementaryCollapse.md)
- Dependency: [D5/S3/Topology/OrdinaryCollarRetraction](../OrdinaryCollarRetraction.md)
- Dependency: [D5/S3/Topology/StableCategory/FourPieceCategoricalCover](FourPieceCategoricalCover.md)
