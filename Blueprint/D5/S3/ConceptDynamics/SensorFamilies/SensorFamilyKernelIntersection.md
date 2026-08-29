# Sensor Family Kernel Intersection

## Abstract

A joint sensor kernel is the intersection of all coordinate kernels.

**Theorem 1.1 (The joint-readout kernel is the coordinate intersection).**

$$\forall sensor: I \to \left(X \to O\right), \operatorname{ker}\left(x \mapsto (i \mapsto \operatorname{sensor}\left(i, x\right))\right) = \operatorname{iInter}\left(i \mapsto \operatorname{ker}\left(\operatorname{sensor}\left(i\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyKernelIntersection.joint_readout_kernel_eq_iInter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

View an indexed sensor family as one function-valued joint readout.

Equality of two joint readouts is equality at every sensor coordinate, and coordinatewise equality reconstructs equality of the functions.

Thus the joint collision set is the intersection over all coordinate kernels, including when the index type is empty or infinite.

## References

- Truth anchor: `D5/S3/ConceptDynamics/SensorFamilies/SensorFamilyKernelIntersection.joint_readout_kernel_eq_iInter`
