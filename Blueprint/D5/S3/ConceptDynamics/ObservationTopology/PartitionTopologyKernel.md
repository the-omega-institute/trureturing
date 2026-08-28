# Partition Topology Kernel

## Abstract

Inseparability in a readout partition topology is exactly equality in the readout kernel.

**Theorem 1.1 (Partition-topology inseparability is equality of readouts).**

$$\forall readout: \operatorname{Concept}\left(X, B\right), x, y: X, \operatorname{Inseparable}\left(\operatorname{partitionTopology}\left(readout\right), x, y\right) \iff readout(x) = readout(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel.partition_inseparable_iff_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The partition topology is induced by the readout into a discrete coordinate space. Every open set is therefore a union of readout fibers.

Equal readouts place two states in the same fiber, so no open set can distinguish them.

If the readouts differ, the preimage of the singleton containing the first readout is open and contains exactly one of the two states. Thus topological inseparability is equivalent to kernel equality.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/PartitionTopologyKernel.partition_inseparable_iff_kernel`
- Dependency: [D5/S3/ConceptDynamics/Epistemic/PartitionKnowledgeNegativeIntrospection](../Epistemic/PartitionKnowledgeNegativeIntrospection.md)
