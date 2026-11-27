# The actual quaternion lifts have positive Gauss sum in odd rank

## Abstract

The Barnes–Wall quaternion trace Gauss sum

**Theorem 1.1 (A spectator slot puts the trace phase in split form).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddGaussSum.tensor_trace_gauss_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddGaussSum.tensor_trace_gauss_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph A. Keller, Ashley Winter Roberts, and Jeremy Roberts (2026). *CFTs with Large Gap from Barnes-Wall Lattice Orbifolds*. DOI: [10.48550/arXiv.2411.13646](https://doi.org/10.48550/arXiv.2411.13646). URL: <https://arxiv.org/abs/2411.13646v2>.

*Commentary.*

The normalized tensor Gram pairs an even row with its complementary odd row. The two Pauli preimages give a complement permutation followed by a square-zero shear. The half Gram vanishes within the two active slots, so the phase has zero basis values. The resulting split quadratic character sum is positive for every odd slot count at least five.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/BarnesWall/OddGaussSum.tensor_trace_gauss_sum`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/BinaryGauss](../BinaryGauss.md)
