# Unbounded one-step category of finite powers

## Abstract

Unbounded one-step category of finite powers

**Theorem 1.1 (Unbounded one-step categorical cover size of finite powers).**

Lean statement: `D5/S3/Topology/StableCategory/UnrestrictedFactorPowers.exists_no_categorical_cover_of_no_one`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/UnrestrictedFactorPowers.exists_no_categorical_cover_of_no_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

The added rank coordinate lets every chain extend to a full-rank chain. Projection has a section using the size of each principal ideal. Raising each rank to the maximum of its old rank and the section rank gives two pointwise comparisons. The subdivision fence lift transports categorical lower covers along these maps. The Hales–Jewett obstruction in the enlarged poset then applies to powers of the original finite poset.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/UnrestrictedFactorPowers.exists_no_categorical_cover_of_no_one`
- Dependency: [D5/S3/Topology/StableCategory/HalesJewettCategoricalCover](HalesJewettCategoricalCover.md)
- Dependency: [D5/S3/Topology/SubdivisionCategoricalCover](../SubdivisionCategoricalCover.md)
