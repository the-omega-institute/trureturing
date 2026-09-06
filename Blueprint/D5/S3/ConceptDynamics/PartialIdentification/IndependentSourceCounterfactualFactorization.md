# Counterfactual factorization from independent disturbances

## Abstract

Elementary independent disturbances supply the block laws needed by the existing intervention-locality compiler, yielding counterfactual factorization on the original full source carrier.

**Theorem 1.1 (Identify direct and partitioned readout laws).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_pair_readout_eq_partitioned`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_pair_readout_eq_partitioned` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pushforward of the original independent source law equals the existing partitioned readout representation with block laws derived from the same elementary disturbances.

**Theorem 1.2 (Factorize separated readouts under the full law).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_separated_readouts_factorize`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_separated_readouts_factorize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Disjoint semantic dependency supports give product response laws. Mutual elementary independence supplies the required block factorization.

**Theorem 1.3 (Evaluate joint cells by actual marginals).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_separated_readouts_cell_eq_product`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_separated_readouts_cell_eq_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every joint response cell is the product of the actual marginals of the full-source pushforward. Boolean simultaneous benefit is the true,true cell.

**Theorem 1.4 (Join structural evaluation to elementary disturbance laws).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.compiled_counterfactual_events_independent_sources`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.compiled_counterfactual_events_independent_sources` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing counterfactual support compiler and source-separation proof are reused unchanged. The theorem takes elementary laws directly, without a separately supplied block-law premise.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.compiled_counterfactual_events_independent_sources`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_pair_readout_eq_partitioned`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_separated_readouts_cell_eq_product`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.independentSource_separated_readouts_factorize`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/FiniteIndependentSourceGrouping](FiniteIndependentSourceGrouping.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization](SeparatedCounterfactualSourceFactorization.md)
