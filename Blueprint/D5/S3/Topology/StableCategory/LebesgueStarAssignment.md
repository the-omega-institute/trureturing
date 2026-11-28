# Weak category two in order-complex dimension four

## Abstract

Weak category two in order-complex dimension four

**Theorem 1.1 (The stable four-piece bound).**

Lean statement: `D5/S3/Topology/StableCategory/LebesgueStarAssignment.four_lower_sets_of_two_categorical_opens`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/LebesgueStarAssignment.four_lower_sets_of_two_categorical_opens` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For a finite poset with connected order-complex realization and order-complex dimension at most four, a cover of the realization by two categorical open sets gives a cover by four categorical lower sets in an ordinary iterated subdivision of the poset.

Each subdivision shrinks the vertex mesh by a factor at most four fifths in the original coordinate metric. Once that bound falls below the Lebesgue number, each closed star is subordinate to a categorical open. The resulting subcomplex inclusions carry the two contractions, and the four-piece construction passes to the iterated chain poset.

**Theorem 1.2 (Categorical subcomplexes subordinate to an open cover).**

Lean statement: `D5/S3/Topology/StableCategory/LebesgueStarAssignment.categorical_subcomplex_cover_of_open_cover`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/StableCategory/LebesgueStarAssignment.categorical_subcomplex_cover_of_open_cover` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Mosquera-Lois and Kohei Tanaka (2026). *Weak, stable, and ordinary Lusternik-Schnirelmann category of finite spaces*. DOI: [10.48550/arXiv.2609.39615](https://doi.org/10.48550/arXiv.2609.39615). URL: <https://arxiv.org/abs/2609.39615v1>.

*Commentary.*

For a finite simplicial complex in arbitrary dimension, a categorical open cover of its realization gives categorical subcomplexes at one common ordinary subdivision depth. Each closed star lies in the subcomplex assigned to its vertex, and its realization maps into the corresponding open set. A uniform bound on face cardinality supplies a mesh contraction factor strictly less than one.

## References

- Truth anchor: `D5/S3/Topology/StableCategory/LebesgueStarAssignment.categorical_subcomplex_cover_of_open_cover`
- Truth anchor: `D5/S3/Topology/StableCategory/LebesgueStarAssignment.four_lower_sets_of_two_categorical_opens`
- Dependency: [D5/S3/Geometry/FiniteVertexCylinder](../../Geometry/FiniteVertexCylinder.md)
- Dependency: [D5/S3/Topology/StableCategory/DimensionFourCategoricalColour](DimensionFourCategoricalColour.md)
