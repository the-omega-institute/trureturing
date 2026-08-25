# Residual Separation Topology

## Abstract

A target defect is exactly a topological separation deficit.

**Theorem 1.1 (The target defect relation equals the separation deficit).**

$$\forall current: \operatorname{Concept}\left(X, Current\right), target: \operatorname{Concept}\left(X, Target\right), \operatorname{defectRelation}\left(current, target\right) = \operatorname{separationDeficit}\left(current, target\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology.defectRelation_eq_separationDeficit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A target defect is a pair of states identified by the current readout but distinguished by the target.

Partition-topology inseparability is exactly equality of the corresponding readout. Current equality is therefore current inseparability, while target inequality is failure of target inseparability.

Extensionality identifies the two sets of pairs. The theorem is an exact set equality and introduces no additional topological condition.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/ResidualSeparationTopology.defectRelation_eq_separationDeficit`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](../DefinitionEscape/ResidualJoinLaw.md)
- Dependency: [D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel](PartitionTopologyKernel.md)
