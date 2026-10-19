# Relabel actual graph histories by vertex and edge equivalences

## Abstract

Relabel actual graph histories by vertex and edge equivalences.

Relabel.symm reverses the given finite graph relabeling and proves its two endpoint laws. Relabel.homeomorph applies the edge equivalence coordinatewise to every legal integer-indexed history, uses the inverse equivalence for its inverse, and proves continuity in the product/subtype topology.

The construction ranges over V,E,W,D : Type* and graphs G,H; it assumes neither Fintype nor inhabitedness. The homeomorphism section assumes TopologicalSpace and DiscreteTopology on E and D. The filename does not strengthen those hypotheses into finiteness. Empty and infinite discrete carriers are not excluded by this API.

These constructions and identities are repository-derived. Their provenance does not assert literature novelty.

**Definition 1.1 (Relabel.symm).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph.symm`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph.symm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reverse the given vertex and edge equivalences and transport both endpoint laws. This constructs the inverse graph relabel on arbitrary carriers.

**Definition 1.2 (Relabel.homeomorph).**

Lean statement: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph.homeomorph`

*Formalization.* `D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph.homeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the edge equivalence at every integer coordinate. Its inverse and continuity follow coordinatewise under the stated discrete edge topologies.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph.homeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/PositiveRecoding/FiniteGraphRelabelHomeomorph.symm`
- Dependency: [D5/S3/ConceptDynamics/Coding/TwoSidedFiniteInduction](../TwoSidedFiniteInduction.md)
