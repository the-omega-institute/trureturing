# Pair Readout Kernel Intersection

## Abstract

The kernel of a paired readout is the intersection of its two kernels.

**Theorem 1.1 (The paired kernel is the component-kernel intersection).**

$$\forall left: X \to Y, right: X \to Z, \operatorname{ker}\left(x \mapsto (\operatorname{left}\left(x\right), \operatorname{right}\left(x\right))\right) = \operatorname{intersection}\left(\operatorname{ker}\left(left\right), \operatorname{ker}\left(right\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SensorFamilies/PairReadoutKernelIntersection.pair_readout_kernel_eq_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pair two arbitrary readouts left and right on the same source type.

Two states have equal paired readouts exactly when both component readouts are equal on those states.

Consequently the set of paired collisions is precisely the intersection of the two component collision sets.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SensorFamilies/PairReadoutKernelIntersection.pair_readout_kernel_eq_intersection`
