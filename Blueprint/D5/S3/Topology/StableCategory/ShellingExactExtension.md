# Exact categorical extension across a shelling step

## Abstract

Exact categorical extension across a shelling step

**Theorem 1.1 (Attachment along a union of facets).**

Lean statement: `D5/S3/Topology/StableCategory/ShellingExactExtension.exact_extension_shelling`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/ShellingExactExtension.exact_extension_shelling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A prescribed categorical two-cover on the retained triangulation extends across one shelling simplex with exact old intersections at the third ordinary barycentric subdivision. Each resulting piece is full and contracts by finite contiguity in the common ambient.

The mixed case uses the set of omitted vertices of the facets in the second piece. It may lie in both old pieces. The two regions at the second subdivision only need to cover vertices. The final subdivision recovers both the cover and the prescribed intersections.

**Theorem 1.2 (Exact retention across an elementary expansion).**

Lean statement: `D5/S3/Topology/StableCategory/ShellingExactExtension.exact_extension_elementary_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/ShellingExactExtension.exact_extension_elementary_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

The shelling theorem applies to the horn of the simplex in an elementary expansion. Connectedness of the expanded complex joins the terminal constants in the monochromatic case.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/ShellingExactExtension.exact_extension_elementary_expansion`
- Truth anchor: `D5/S3/Topology/StableCategory/ShellingExactExtension.exact_extension_shelling`
- Dependency: [D5/S3/Topology/StableCategory/DepthZeroElementaryExpansion](DepthZeroElementaryExpansion.md)
- Dependency: [D5/S3/Topology/StableCategory/MixedSimplexAttachment](MixedSimplexAttachment.md)
