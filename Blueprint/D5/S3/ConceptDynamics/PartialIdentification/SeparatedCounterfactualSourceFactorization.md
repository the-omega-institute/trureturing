# Counterfactual source separation and product laws

## Abstract

Intervention-specific dependency certificates discharge the coordinatewise-map premise of finite product pushforward. Independent source blocks retain arbitrary internal coupling.

**Definition 1.1 (Partition the full source carrier).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.partitionedReadoutLaw`

*Formalization.* `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.partitionedReadoutLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib piEquivPiSubtypeProd recoordinates every original source assignment into a supported block and its complement. The readouts themselves remain the original full-source functions.

**Theorem 1.2 (Obtain product response laws from disjoint supports).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.separated_readouts_factorize`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.separated_readouts_factorize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

DependsOn gives reduced maps through coordinate restriction. Disjoint support puts the right map in the complement block, allowing reuse of the existing product-pushforward theorem. Independence inside either block is unnecessary.

**Theorem 1.3 (Evaluate joint cells from the actual marginals).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.separated_readouts_cell_eq_product`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.separated_readouts_cell_eq_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every joint response cell equals the product of its actual marginal masses. At the Boolean cell true,true this is the joint-benefit formula. It is a probability-evaluation corollary of the preceding factorization.

**Theorem 1.4 (Connect structural evaluation to cross-world factorization).**

Lean statement: `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.compiled_counterfactual_events_factorize`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.compiled_counterfactual_events_factorize` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof combines parent-indexed structural semantics, local exogenous contracts, compiled support descent, support disjointness, and an explicit independent block law. A c-component label alone supplies none of the required event-locality evidence.

## References

- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.compiled_counterfactual_events_factorize`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.partitionedReadoutLaw`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.separated_readouts_cell_eq_product`
- Truth anchor: `D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.separated_readouts_factorize`
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/InterventionExogenousLocality](InterventionExogenousLocality.md)
- Dependency: [D5/S3/ConceptDynamics/PartialIdentification/MarkovianResponseLawFactorization](MarkovianResponseLawFactorization.md)
