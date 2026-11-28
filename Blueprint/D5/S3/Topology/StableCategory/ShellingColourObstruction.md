# Induced cycles obstruct mixed shelling restrictions

## Abstract

Induced cycles obstruct mixed shelling restrictions

**Theorem 1.1 (Monochromatic induced four-cycles and shelling restrictions).**

Lean statement: `D5/S3/Topology/StableCategory/ShellingColourObstruction.false_of_monochromatic_four_cycle`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/ShellingColourObstruction.false_of_monochromatic_four_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

In a shelling starting with a simplex, a monochromatic induced four-cycle would have to survive when the last facet is removed. A newly introduced cycle vertex would put both neighbours in the attaching simplex and create a diagonal. Once the vertices are already present, the mixing requirement forces the four edges into the preceding prefix as well. The cycle would therefore lie in the initial simplex, which contains its diagonals.

**Theorem 1.2 (Obstruction after barycentric subdivision in dimension at least eight).**

Lean statement: `D5/S3/Topology/StableCategory/ShellingColourObstruction.false_of_mixed_restrictions_sd_of_nine_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/ShellingColourObstruction.false_of_mixed_restrictions_sd_of_nine_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

A simplex with nine vertices yields three independent triples in the face-comparability graph, with all edges across triples. Two triples have the same majority colour, giving a monochromatic induced four-cycle. Consequently every positive barycentric iterate of a complex of dimension at least eight has this obstruction to the mixed restriction-face criterion.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/ShellingColourObstruction.false_of_mixed_restrictions_sd_of_nine_vertices`
- Truth anchor: `D5/S3/Topology/StableCategory/ShellingColourObstruction.false_of_monochromatic_four_cycle`
- Dependency: [D5/S3/Geometry/FiniteAlexanderDualCollapse](../../Geometry/FiniteAlexanderDualCollapse.md)
- Dependency: [D5/S3/Topology/BarycentricBaseRigidity](../BarycentricBaseRigidity.md)
