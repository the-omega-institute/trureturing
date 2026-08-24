# Definition Universe and Kernel Order

## Abstract

Definitions form a dependent universe ordered by their equality kernels.

**Theorem 1.1 (The definition universe carries its kernel and higher-order constructors).**

$$\operatorname{Def}\left(X\right) = \Sigma_{D: U} X \to D,\\{}\operatorname{ker}\left(d\right) = \operatorname{SetoidKer}\left(d\right), \operatorname{Im}\left(d\right) = \operatorname{range}\left(d\right),\\{}\operatorname{DefinitionEquivalent}\left(d, e\right) \Leftrightarrow \operatorname{ker}\left(d\right) = \operatorname{ker}\left(e\right), \operatorname{DefinitionRefines}\left(d, e\right) \Leftrightarrow \operatorname{ker}\left(e\right) \subseteq \operatorname{ker}\left(d\right),\\{}\operatorname{DefinitionEquivalent}\left(d, e\right) \Leftrightarrow (\operatorname{DefinitionRefines}\left(d, e\right) \land \operatorname{DefinitionRefines}\left(e, d\right)), (\operatorname{Im}\left(d\right) = \mathrm{univ}) \Leftrightarrow \operatorname{Surjective}\left(d\right),\\{}\operatorname{MetaDef}\left(X\right) = \operatorname{Def}\left(\operatorname{Def}\left(X\right)\right), \operatorname{Generator}\left(X, S\right) = S \to \operatorname{Def}\left(X\right),\\{}\operatorname{Transformer}\left(X, Y\right) = \operatorname{Def}\left(X\right) \to \operatorname{Def}\left(Y\right), \operatorname{Method}\left(X\right) = \operatorname{DState}\left(X\right) \times \operatorname{Residual}\left(X\right) \to \operatorname{Def}\left(X\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionUniverseKernel.definition_universe_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A definition on X is a dependent pair: its first projection is a codomain in the same universe and its second projection is the canonical Concept readout from X. Its kernel is delegated to Setoid.ker and its realized image to Set.range.

Conceptual equivalence is literal equality of source kernels. The coarse-to-fine relation reverses kernel inclusion, so equality holds exactly when both directed refinements hold. The realized image is universal exactly when the packaged readout is surjective.

MetaDef applies the same Sigma construction to Def X. Generators are S-indexed families, transformers map one definition universe to another, and a method consumes the paired definition and residual states to choose the next packaged definition.

The repository's Refines relation is factorization rather than raw kernel inclusion. Separate bridge declarations apply the accepted concept-kernel order duality only for surjective readouts, where the two notions coincide. Boolean examples witness both a proper refinement and a realized image that omits a coordinate.

**Theorem 1.2 (Definition packaging determines its kernel and realized image).**

$$\forall X: \operatorname{Type}_{u}, definition: \operatorname{Def}\left(X\right), ((\operatorname{Def}\left(X\right) = \Sigma_{D: \operatorname{Type}_{u}} {X \to D}) \land (\exists D: \operatorname{Type}_{u}, d: X \to D, definition = \langle D, d\rangle)) \land\\{}(\forall x, y: X, \operatorname{ker}\left(definition\right)(x, y) \Leftrightarrow definition.2(x) = definition.2(y)) \land\\{}(\forall z: definition.1, z \in \operatorname{Im}\left(definition\right) \Leftrightarrow \exists x: X, definition.2(x) = z).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionUniverseKernel.definition_universe_kernel_and_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each packaged definition on X, the conjunction states exactly its Sigma codomain-readout form, its pointwise equality kernel, and membership in its realized image. It adds no surjectivity, refinement, equivalence, or higher-order constructor claim.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionUniverseKernel.definition_universe_kernel`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionUniverseKernel.definition_universe_kernel_and_image`
- Dependency: [D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence](../Interventions/RedundantAppealDefectPersistence.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/ConceptKernelOrderDuality](../Refinement/ConceptKernelOrderDuality.md)
