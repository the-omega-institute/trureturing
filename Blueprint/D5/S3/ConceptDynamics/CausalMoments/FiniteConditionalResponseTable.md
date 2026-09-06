# One common-source realization for all strata

## Abstract

Existence quantifies over one pair of complete disturbances, rather than separate models for each stratum.

**Definition 1.1 (A row distribution from a fixed table).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.tableEvaluationLaw`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.tableEvaluationLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Push a complete response-table law through evaluation at one covariate value.

**Theorem 1.2 (All row marginals in one disturbance).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.tableEvaluationLaw_independentSource`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.tableEvaluationLaw_independentSource` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product law on full tables reproduces every prescribed row law. Dependence among coordinates inside a response value is unrestricted.

**Theorem 1.3 (Simultaneous finite conditional representation).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.finite_conditional_table_realization`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.finite_conditional_table_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One normalized rational table law realizes the entire conditional response family.

**Definition 1.4 (Two complete response mechanisms).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.FixedNoisePairModel`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.FixedNoisePairModel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each mechanism has one law on complete tables. The model class permits arbitrary dependence between different rows.

**Definition 1.5 (Independent covariate and mechanism disturbances).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.fixedNoiseSourceLaw`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.fixedNoiseSourceLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common source law is the product of the covariate root law and the two full-table laws.

**Definition 1.6 (Read the same stratum from both tables).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.selectedPairLaw`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.selectedPairLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A deterministic map selects each mechanism response at the common covariate value.

**Theorem 1.7 (Exact selected response law).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.selectedPairLaw_mass`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.selectedPairLaw_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each joint cell equals the covariate mass times the two actual row marginal masses. This division-free statement includes zero-weight strata.

**Definition 1.8 (Canonical simultaneous witness).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.canonicalFixedNoisePair`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.canonicalFixedNoisePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Independent rows construct one attaining table per mechanism. Row independence is a choice of witness and is not imposed on the general model class.

**Theorem 1.9 (Realize every specified conditional cell).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.canonicalFixedNoisePair_selected_mass`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.canonicalFixedNoisePair_selected_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical fixed-noise model reproduces both conditional response kernels at every covariate value.

**Theorem 1.10 (One common-source realization for all strata).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.simultaneous_conditional_product_realization`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.simultaneous_conditional_product_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Existence quantifies over one pair of complete disturbances, rather than separate models for each stratum.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.FixedNoisePairModel`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.canonicalFixedNoisePair`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.canonicalFixedNoisePair_selected_mass`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.finite_conditional_table_realization`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.fixedNoiseSourceLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.selectedPairLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.selectedPairLaw_mass`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.simultaneous_conditional_product_realization`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.tableEvaluationLaw`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/FiniteConditionalResponseTable.tableEvaluationLaw_independentSource`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping](../PartialIdentification/FiniteIndependentSourceGrouping.md)
