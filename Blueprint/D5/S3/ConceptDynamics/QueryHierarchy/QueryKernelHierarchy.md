# Observation Intervention Counterfactual Kernel Hierarchy

## Abstract

Collapse maps between query laws force a descending equality-kernel chain, and a concrete three-layer query system realizes strictness in both steps.

**Theorem 1.1 (Query-law kernel chain).**

$$\forall o, i, c, a, b, \operatorname{ker}(c) \subseteq \operatorname{ker}(i) \land \operatorname{ker}(i) \subseteq \operatorname{ker}(o)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/QueryHierarchy/QueryKernelHierarchy.query_kernel_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generic clauses use explicit collapse maps between observation, intervention, and counterfactual laws, so equality of a richer profile is transported to every coarser profile.

**Theorem 1.2 (Both inclusions can be strict).**

$$\operatorname{ker}(layeredCounterfactual) \subseteq \operatorname{ker}(layeredIntervention) \land \operatorname{ker}(layeredIntervention) \subseteq \operatorname{ker}(layeredObservation) \land strictnessWitnesses$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/QueryHierarchy/QueryKernelHierarchy.observation_intervention_counterfactual_kernel_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The concrete three-coordinate query laws expose a pair witnessing each strict inclusion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/QueryHierarchy/QueryKernelHierarchy.observation_intervention_counterfactual_kernel_chain`
- Truth anchor: `D5/S3/ConceptDynamics/QueryHierarchy/QueryKernelHierarchy.query_kernel_chain`
