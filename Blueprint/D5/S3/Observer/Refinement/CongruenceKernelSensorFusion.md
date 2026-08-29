# Congruence Kernel Sensor Fusion

## Abstract

Forward-congruence completion commutes with arbitrary sensor intersections.

**Theorem 1.1 (Congruence kernel commutes with sensor intersections).**

$$\forall tau: Y \to Y, R: I \to \operatorname{StateRelation}\left(Y\right),\\{}\operatorname{congruenceKernel}\left(tau, \operatorname{iInter}\left(i \mapsto \operatorname{R}\left(i\right)\right)\right) = \operatorname{iInter}\left(i \mapsto \operatorname{congruenceKernel}\left(tau, \operatorname{R}\left(i\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Refinement/CongruenceKernelSensorFusion.congruence_kernel_iInter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a state endomorphism and an arbitrary indexed family of state relations.

Membership in the congruence kernel of the intersection means that every iterate lies in every sensor relation.

Exchanging the universal quantifiers over iterates and sensor indices gives the intersection of the individual congruence kernels. No finiteness of the sensor index is required.

## References

- Truth anchor: `D5/S3/Observer/Refinement/CongruenceKernelSensorFusion.congruence_kernel_iInter`
- Dependency: [D5/S3/Observer/Separation/CongruenceKernel](../Separation/CongruenceKernel.md)
