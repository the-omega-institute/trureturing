# A relative two-cover at the second subdivision

## Abstract

A relative two-cover at the second subdivision

**Theorem 1.1 (Two lower regions retract into the common inherited region after two subdivisions).**

Lean statement: `D5/S3/Topology/StableCategory/RelativeMaximaDoubleSubdivision.exists_relative_two_cover_double_subdivision`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/RelativeMaximaDoubleSubdivision.exists_relative_two_cover_double_subdivision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

Choose maximal elements of a finite poset with at least one strict predecessor for each. One region consists of flags whose chains all meet the old poset and contracts into it by intersection. The other consists of old flags and separate components in which every chain contains the same chosen maximum. Insert its singleton, move the component to it, and follow an ambient path of flags to an old predecessor. Both regions contain and fix the entire inherited region. If the old inclusion is categorical, the same relative homotopies give a categorical lower two-cover.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/RelativeMaximaDoubleSubdivision.exists_relative_two_cover_double_subdivision`
- Dependency: [D5/S3/Topology/DescendingClosureContiguity](../DescendingClosureContiguity.md)
- Dependency: [D5/S3/Topology/StableCategory/RelativeCoverNecessity](RelativeCoverNecessity.md)
- Dependency: [D5/S3/Topology/SubdivisionCategoricalCover](../SubdivisionCategoricalCover.md)
