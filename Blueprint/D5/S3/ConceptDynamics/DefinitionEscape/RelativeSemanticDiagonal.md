# Relative Semantic Diagonal

## Abstract

Complete decoder catalogs yield diagonal targets outside the latent closure.

**Theorem 1.1 (A complete decoder catalog leaves a nonempty blind residual).**

$$\operatorname{Nonempty}\left(X\right) \land \operatorname{FixedPointFree}\left(twist\right) \land \operatorname{Surjective}\left(decoderCatalog\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{blindResidual}\left(Gamma, current, \operatorname{relativeSemanticDiagonal}\left(twist, \operatorname{languageExtension}\left(current, \operatorname{familyReadout}\left(Gamma\right)\right), decoderCatalog\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/RelativeSemanticDiagonal.complete_catalog_diagonal_blindResidual_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The diagonal target uses languageExtension, a decoder catalog, and a fixed-point-free twist; blindResidual remains canonical.

Surjectivity puts every decoder at an address where the diagonal differs, and the recovery criterion turns inadequacy into a nonempty blind residual.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/RelativeSemanticDiagonal.complete_catalog_diagonal_blindResidual_nonempty`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](DefinitionKernelGalois.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/QuestionAlgebraDuality](QuestionAlgebraDuality.md)
