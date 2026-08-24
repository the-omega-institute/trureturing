# Complete Query Kernel Hierarchy

## Abstract

The public theorem combines the generic query-law kernel chain with explicit witnesses for strictness in both inclusions.

**Theorem 1.1 (Query-law kernel hierarchy with strictness).**

$$\operatorname{ker}(counterfactualLaw) \subseteq \operatorname{ker}(interventionLaw) \land \operatorname{ker}(interventionLaw) \subseteq \operatorname{ker}(observationLaw) \land strictnessWitnesses$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/QueryLaws/QueryKernelHierarchyComplete.query_kernel_hierarchy_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first public conjunct is generic in the model and law carriers and uses only the two source collapse premises. The remaining conjuncts are concrete Boolean-coordinate countermodels.

## References

- Truth anchor: `D5/S3/ConceptDynamics/QueryLaws/QueryKernelHierarchyComplete.query_kernel_hierarchy_complete`
- Dependency: [D5/S3/ConceptDynamics/Interventions/QueryKernelHierarchy](../Interventions/QueryKernelHierarchy.md)
