# Naturality of two face cuts in ordinary subdivision

## Abstract

Naturality of two face cuts in ordinary subdivision

**Theorem 1.1 (Transport original supports under ordinary subdivision).**

Lean statement: `D5/S3/Topology/OrdinarySubdivisionMap.originalSupport_image`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrdinarySubdivisionMap.originalSupport_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Applying a simplicial vertex map to an iterated subdivision sends each original support to its image under that map. The map can identify vertices.

**Theorem 1.2 (Detect the retained vertices through a colour-preserving map).**

Lean statement: `D5/S3/Topology/OrdinarySubdivisionMap.inTwoCutCollar_iterate_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrdinarySubdivisionMap.inTwoCutCollar_iterate_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For a colour-preserving simplicial map, a vertex of the third subdivision survives both face cuts exactly when its image survives them.

**Theorem 1.3 (Compute the support of the two cuts).**

Lean statement: `D5/S3/Topology/OrdinarySubdivisionMap.mem_twoCutImage_support`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrdinarySubdivisionMap.mem_twoCutImage_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

The nested image flags carry exactly the original vertices of the selected colour. Removing empty intersections and identifying repeated entries preserves their union.

**Theorem 1.4 (Transport the two-cut image through a colour-preserving map).**

Lean statement: `D5/S3/Topology/OrdinarySubdivisionMap.twoCutImage_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/OrdinarySubdivisionMap.twoCutImage_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Intersecting old faces with one colour, deleting empty entries, and taking the successive images of flags commute with a colour-preserving simplicial map.

## References

- Truth anchor: `D5/S3/Topology/OrdinarySubdivisionMap.inTwoCutCollar_iterate_iff`
- Truth anchor: `D5/S3/Topology/OrdinarySubdivisionMap.mem_twoCutImage_support`
- Truth anchor: `D5/S3/Topology/OrdinarySubdivisionMap.originalSupport_image`
- Truth anchor: `D5/S3/Topology/OrdinarySubdivisionMap.twoCutImage_iterate`
- Dependency: [D5/S3/Topology/GraphSubdivisionIntervals](GraphSubdivisionIntervals.md)
