# Joint Readout Supremum

## Abstract

A paired readout has the intersection kernel and is the least common refinement of its two coordinates.

**Theorem 1.1 (Pair Readout Kernel).**

$$\forall X: Type, Y: Type, Z: Type, first: Concept X Y, second: Concept X Z,\\{}(Setoid.ker (pairReadout first second) = Setoid.ker first infimum Setoid.ker second).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Refinement/JointReadoutSupremum.pair_readout_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality under the joint readout is exactly equality under both component readouts.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/ObserverMemory/Refinement/JointReadoutSupremum.pair_readout_kernel`
- Dependency: [D5/S3/ConceptDynamics/SensorFamilies/PairReadoutKernelIntersection](../../ConceptDynamics/SensorFamilies/PairReadoutKernelIntersection.md)
- Dependency: [D5/S3/ObserverMemory/Refinement/FactorizationCategory](FactorizationCategory.md)
