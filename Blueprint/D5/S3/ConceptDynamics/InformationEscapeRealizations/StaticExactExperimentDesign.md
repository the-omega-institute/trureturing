# Static Exact Experiment Design Realization

## Abstract

The frozen static exact-design theorem realizes the typed two-CUT law.

**Theorem 1.1 (Legacy realization equivalence).**

$$\operatorname{LegacyPrimitiveRealization}\left(staticExactExperimentArena, StaticExactDesignStatement, staticExactExperimentRealization\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions unfold the concrete experiment response table.

**Theorem 1.2 (Three kernel classes).**

$$\operatorname{card}\left(signatureClasses\right) = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three model indices have three distinct two-bit signatures.

**Theorem 1.3 (Private pair separation).**

$$\operatorname{Not}\left(\operatorname{agrees}\left(staticExactExperimentRealization, 0, 1\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The change-X readout separates model zero from model one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign](../InformationEscapeArenas/StaticExactExperimentDesign.md)
