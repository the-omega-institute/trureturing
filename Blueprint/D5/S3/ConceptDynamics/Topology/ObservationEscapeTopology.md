# Observation Escape Topology

## Abstract

Kernel refinement and productive separation include empty-source primitive escape.

**Theorem 1.1 (Primitive escape is strict partition refinement).**

$$\begin{gathered}\forall X, InputOutput, Output: \operatorname{Type},\\{}Gamma: \operatorname{Set}\left(\operatorname{Concept}\left(X, InputOutput\right)\right),\\{}candidate: \operatorname{Concept}\left(X, Output\right),\\{}(\operatorname{PrimitiveEscape}\left(Gamma, candidate\right) \iff \operatorname{partitionTopology}\left(\operatorname{extendedFamilyReadout}\left(Gamma, candidate\right)\right) < \operatorname{partitionTopology}\left(\operatorname{familyReadout}\left(Gamma\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/ObservationEscapeTopology.primitiveEscape_iff_strict_partition_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete family readout records every old definition, while the extended readout pairs those coordinates with the candidate value.

Primitive escape is equivalent to strict refinement from the old partition topology to the extended one, with Mathlib's reversed order on topologies displayed explicitly.

No inhabited-source hypothesis is required. On an empty source, both primitive escape and strict refinement are false, so the biconditional remains valid without asserting an escape.

**Theorem 1.2 (Productive separation is a topological target split).**

$$\begin{gathered}\forall X, Current, InputOutput, Target, Output: \operatorname{Type},\\{}Gamma: \operatorname{Set}\left(\operatorname{Concept}\left(X, InputOutput\right)\right),\\{}current: \operatorname{Concept}\left(X, Current\right),\\{}target: \operatorname{Concept}\left(X, Target\right),\\{}candidate: \operatorname{Concept}\left(X, Output\right),\\{}(\operatorname{ProductiveSeparation}\left(Gamma, current, target, candidate\right) \iff\\{}(\exists left, right: X, \operatorname{Inseparable}\left(\operatorname{partitionTopology}\left(current\right), left, right\right) \land\\{}\neg \operatorname{Inseparable}\left(\operatorname{partitionTopology}\left(target\right), left, right\right) \land\\{}\operatorname{Inseparable}\left(\operatorname{partitionTopology}\left(\operatorname{familyReadout}\left(Gamma\right)\right), left, right\right) \land\\{}\neg \operatorname{Inseparable}\left(\operatorname{partitionTopology}\left(candidate\right), left, right\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/ObservationEscapeTopology.productiveSeparation_iff_topological_target_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A productive separation is witnessed by two source states that the current readout cannot separate but the target can.

The same states remain inseparable under the joint readout of the complete old family, while the candidate partition topology separates them.

The biconditional packages exactly these four inseparability and separation clauses. It adds no inhabitedness, finiteness, or continuity hypothesis.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/ObservationEscapeTopology.primitiveEscape_iff_strict_partition_refinement`
- Truth anchor: `D5/S3/ConceptDynamics/Topology/ObservationEscapeTopology.productiveSeparation_iff_topological_target_split`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois](../DefinitionEscape/DefinitionKernelGalois.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel](../ObservationTopology/PartitionTopologyKernel.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/PrimitiveEscapeStrictRefinement](../ObservationTopology/PrimitiveEscapeStrictRefinement.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology](../ObservationTopology/ResidualSeparationTopology.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/SemanticClosureTopologyInvariance](../ObservationTopology/SemanticClosureTopologyInvariance.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization](../ObservationTopology/TargetContinuityFactorization.md)
