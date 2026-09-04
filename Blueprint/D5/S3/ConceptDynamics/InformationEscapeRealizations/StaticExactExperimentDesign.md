# Static Exact Experiment Design Realization

## Abstract

The frozen static exact-design theorem realizes the typed two-CUT law.

**Definition 1.1 (Concrete static exact-design realization).**

Lean statement: `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.staticExactExperimentRealization`

*Formalization.* `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.staticExactExperimentRealization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The primitive realization assigns the change-X and change-Y Boolean response tables to the two CUT slots.

**Theorem 1.2 (Legacy realization equivalence).**

$${let changeX=(model: \operatorname{Fin}\left(3\right) \mapsto \operatorname{decide}\left(model = 1\right)); changeY=(model: \operatorname{Fin}\left(3\right) \mapsto \operatorname{decide}\left(model = 2\right));\\{}{\forall experiment: Bool, \neg \operatorname{Injective}\left((model \mapsto \operatorname{if}\left(experiment, changeY\left(model\right), changeX\left(model\right)\right))\right)} \land\\{}\operatorname{Injective}\left(\operatorname{jointReadout}\left((experiment: Bool \mapsto \operatorname{if}\left(experiment, changeY, changeX\right))\right)\right) \land\\{}{\forall selected: \operatorname{Finset}\left(Bool\right), \operatorname{Injective}\left(\operatorname{jointReadout}\left((selectedExperiment: \left\{candidate \mid candidate \in selected\right\} \mapsto \operatorname{if}\left(\operatorname{val}\left(selectedExperiment\right), changeY, changeX\right))\right)\right) \implies selected = \left\{false, true\right\}}} \iff staticExactExperimentArena.Law(staticExactExperimentRealization).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both directions unfold the concrete experiment response table.

**Theorem 1.3 (Three kernel classes).**

$$(Finset.univ.image((model: \operatorname{Fin}\left(3\right) \mapsto (staticExactExperimentRealization.readout((0: StaticReadout), model), staticExactExperimentRealization.readout((1: StaticReadout), model))))).card = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_partition_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three model indices have three distinct two-bit signatures.

**Theorem 1.4 (Private pair separation).**

$$\neg staticExactExperimentRealization.toPrimitiveBundle.agrees((0: \operatorname{Fin}\left(3\right)), 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_private_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The change-X readout separates model zero from model one.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.staticExactExperimentRealization`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_partition_count`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_private_pair`
- Truth anchor: `D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.static_exact_design_realization`
- Dependency: [D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign](../InformationEscapeArenas/StaticExactExperimentDesign.md)
