# All-depth rigidity of the base of a relative cone

## Abstract

All-depth rigidity of the base of a relative cone

**Theorem 1.1 (The retained base vertices are fixed under contiguity).**

Lean statement: `D5/S3/Topology/RelativeConeRigidity.relative_cone_all_depth_obstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/RelativeConeRigidity.relative_cone_all_depth_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Suppose every base vertex lies in two distinct facets and the intersection of its incident facets is that vertex. After a positive number of relative subdivisions, each retained base facet has a unique exterior tip, distinct from the tips of other facets. The tip distinction and the facet intersections give the maximal-face criterion. Every contiguity chain starting from the same-depth inclusion after any further ordinary subdivision fixes the retained base vertices.

## References

- Truth anchor: `D5/S3/Topology/RelativeConeRigidity.relative_cone_all_depth_obstruction`
- Dependency: [D5/S3/Geometry/FiniteRelativeSimplicialCollapse](../Geometry/FiniteRelativeSimplicialCollapse.md)
- Dependency: [D5/S3/Topology/BarycentricBaseRigidity](BarycentricBaseRigidity.md)
- Dependency: [D5/S3/Topology/RelativeDerivedContiguity](RelativeDerivedContiguity.md)
