# The Barnes–Wall quaternion trace sign

## Abstract

The Barnes–Wall quaternion trace sign

**Theorem 1.1 (Gauss sum on the common displacement image).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8TraceSign.defect_ground_gauss_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8TraceSign.defect_ground_gauss_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph A. Keller, Ashley Winter Roberts, and Jeremy Roberts (2026). *CFTs with Large Gap from Barnes-Wall Lattice Orbifolds*. DOI: [10.48550/arXiv.2411.13646](https://doi.org/10.48550/arXiv.2411.13646). URL: <https://arxiv.org/abs/2411.13646v2>.

*Commentary.*

The rank-128 tensor basis and strict-lower-triangular lift phases give two displacement maps from the quaternion generators. Their images coincide and are spanned by the 64 even binary labels.

On the common image the trace-product exponent has a perfect cross pairing between the 32 coordinates on each side of the third-bit split. An involutive shear reduces the sign sum to 32 copies of the binary hyperbolic sum, giving the positive value 2^32. This is the finite trace calculation used in the anomaly argument for Conjecture 5.2.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/BarnesWall/Q8TraceSign.defect_ground_gauss_sum`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/BinaryGauss](../BinaryGauss.md)
