# The joint kernel of the two detectors

## Abstract

The joint kernel of the two detectors.

**Theorem 1.1 (The cubic multiplication range).**

Lean statement: `D5/S3/Arith/Partitions/BilgiciThetaJointKernel.joint_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Partitions/BilgiciThetaJointKernel.joint_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Göksal Bilgici (2026). *Nine-Colored Partition Components Modulo 19*. DOI: [10.48550/arXiv.2611.24516](https://doi.org/10.48550/arXiv.2611.24516). URL: <https://arxiv.org/html/2611.24516v1#S8.I1.i1>.

*Commentary.*

On the character-four subspace of degree seven and weight eleven, the joint kernel is exactly the image of multiplication by the invariant cubic from degree four and weight nine of the same character. Two projected words give independent detector columns, and two cubic multiples are independent by their trace coefficients. The four-word upper bound then makes these four classes a basis.

**Theorem 1.2 (Coordinates after the detector tests).**

Lean statement: `D5/S3/Arith/Partitions/BilgiciThetaJointKernel.kernel_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Partitions/BilgiciThetaJointKernel.kernel_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Göksal Bilgici (2026). *Nine-Colored Partition Components Modulo 19*. DOI: [10.48550/arXiv.2611.24516](https://doi.org/10.48550/arXiv.2611.24516). URL: <https://arxiv.org/html/2611.24516v1#S8.I1.i1>.

*Commentary.*

If the tests vanish on a class in the component, both projected-word coefficients are zero. The class is then a linear combination of the two cubic multiples.

## References

- Truth anchor: `D5/S3/Arith/Partitions/BilgiciThetaJointKernel.joint_kernel`
- Truth anchor: `D5/S3/Arith/Partitions/BilgiciThetaJointKernel.kernel_coordinates`
- Dependency: [D5/S3/Arith/Partitions/BilgiciThetaDetectors](BilgiciThetaDetectors.md)
- Dependency: [D5/S3/Arith/Partitions/BilgiciThetaStraightening](BilgiciThetaStraightening.md)
