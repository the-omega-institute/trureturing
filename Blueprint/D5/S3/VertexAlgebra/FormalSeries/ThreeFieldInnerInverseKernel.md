# The coupled inner inverse kernel

## Abstract

The coupled inner inverse kernel

**Theorem 1.1 (The varying inverse order 2k+r).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerInverseKernel.inner_inverse_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerInverseKernel.inner_inverse_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The middle binomial kernel and the second difference kernel combine by the integer-binomial shift identity and the binomial-series group law. Their coefficient at S^r T^s is (-1)^s binom(-k,r) binom(-(2k+r),s-r) when r <= s. Convolution with (1+S)^(-H) gives the stated finite l sum. Every spectator degree and zero exponent is included. The binomial-series suppliers retain Scott Carnahan attribution.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerInverseKernel.inner_inverse_coeff`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerLaurentFiber](ThreeFieldInnerLaurentFiber.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/ThreeFieldInnerNativeInverse](ThreeFieldInnerNativeInverse.md)
