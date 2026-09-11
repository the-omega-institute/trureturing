# Context Extension Composition

## Abstract

Sequential context embeddings compose, and their new-region charges add.

**Proposition 1.1 (Composition transports q and splits the new region).**

$$\operatorname{q}\left(E, \operatorname{k}\left(\operatorname{j}\left(A\right)\right)\right) = \operatorname{q}\left(C, A\right), R_{jk} = R_{k} \cup \operatorname{k}\left(R_{j}\right) \land \left(\operatorname{Disjoint}\left(R_{k}, \operatorname{k}\left(R_{j}\right)\right) \land \operatorname{charge}\left(E, R_{jk}\right) = \operatorname{charge}\left(E, R_{k}\right) + \operatorname{charge}\left(E, \operatorname{k}\left(R_{j}\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComposition.context_extension_composition_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Given embeddings j from C to D and k from D to E, their archive and current-region maps compose. The new region of the composite is the disjoint union of the second new region and the image of the first new region.

The signed charge therefore adds across the two extension steps, while the selected q readout is transported unchanged through both maps.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Spacetime/ContextExtensionComposition.context_extension_composition_spec`
- Dependency: [D5/S3/ConceptDynamics/Spacetime/ContextExtensionComplement](ContextExtensionComplement.md)
