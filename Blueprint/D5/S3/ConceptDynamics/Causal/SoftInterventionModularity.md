# Soft Intervention Modularity

## Abstract

Finite DAG mechanism modules support local kernel replacement, with modularity required for the formula.

**Definition 1.1 (Finite mechanism module).**

Lean statement: `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.mechanismModule`

*Formalization.* `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.mechanismModule` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A mechanism module assigns a finite parent-indexed PMF to every DAG node.

**Definition 1.2 (Soft intervention).**

Lean statement: `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.softIntervention`

*Formalization.* `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.softIntervention` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A soft intervention replaces exactly the selected node mechanisms and leaves all other mechanisms unchanged.

**Theorem 1.3 (Local replacement formula).**

$$jointLaw\left(softIntervention\left(base, I, replacement\right), x\right) = prod\left(i, I, replacement\left(i, x\right)\right) \times prod\left(v, VminusI, base\left(v, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.local_replacement_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint mass factors into the selected replacement kernels and the unchanged kernels.

**Theorem 1.4 (Modularity is necessary).**

$$linkedJointLaw\left(x\right) \ne localReplacementProduct\left(I, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.modularity_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A device that changes a root and its child together disagrees with the local formula that keeps the child mechanism fixed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.local_replacement_formula`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.mechanismModule`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.modularity_is_necessary`
- Truth anchor: `D5/S3/ConceptDynamics/Causal/SoftInterventionModularity.softIntervention`
