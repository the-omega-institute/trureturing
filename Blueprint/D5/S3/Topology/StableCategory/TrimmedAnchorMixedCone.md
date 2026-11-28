# An exclusive-vertex anchor for a relative cone cover

## Abstract

An exclusive-vertex anchor for a relative cone cover

**Theorem 1.1 (A full first trace and an anchor on the other trace give an exact categorical two-cover).**

Lean statement: `D5/S3/Topology/StableCategory/TrimmedAnchorMixedCone.trimmed_anchor_exact_two_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/TrimmedAnchorMixedCone.trimmed_anchor_exact_two_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Suppose the first trace on the cone base is full. Assign each exterior face with a vertex in that trace to the first piece. Trim to its first-trace vertices and then remove the apex. On the other side, adjoin one vertex that spans every base face supported entirely outside the first trace, then remove the apex. The resulting point cover preserves each old region pointwise along its relative order fence. The two regions become a categorical lower cover after two ordinary subdivisions, with the prescribed old intersections.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/TrimmedAnchorMixedCone.trimmed_anchor_exact_two_cover`
- Dependency: [D5/S3/Topology/BarycentricGraphDistance](../BarycentricGraphDistance.md)
- Dependency: [D5/S3/Topology/StableCategory/RelativeMaximaDoubleSubdivision](RelativeMaximaDoubleSubdivision.md)
