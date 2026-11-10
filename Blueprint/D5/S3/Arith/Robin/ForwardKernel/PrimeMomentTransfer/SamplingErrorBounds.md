# Sampling error bounds

## Abstract

Fourth moments control continuous sampling and weighted finite product replacement.

**Theorem 1.1 (Weighted product replacement).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds.weighted_product_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds.weighted_product_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On [1,2] with restricted Lebesgue measure, let 1<=k<=4 and let both families belong to L4, with fourth integrals at most K and fourth difference integrals at most D. For an integrable weight of absolute value at most B, the difference of its two product integrals is at most B k D^(1/4) K^((k-1)/4).

**Theorem 1.2 (Uniform continuous and sampled fourth moments).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds.uniform_sampling_fourth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds.uniform_sampling_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume singular-series values one on the empty set and singletons, MeanSquareHL4(SS,beta) and the interval correlation bounds, with 0<alpha<beta<1/4 and M>=1. There is C>=1 such that, for every positive delta and all sufficiently large N, both normalized continuous and floor sampled increments belong to L4 on [1,2], both fourth integrals are at most C, and their fourth difference integral is at most delta^4, uniformly in natural H between N^alpha and N^beta and 0<=a<=b<=M.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds.uniform_sampling_fourth`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SamplingErrorBounds.weighted_product_difference`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds](CellMomentBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling](ContinuousSampling.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates](UniformRates.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools](WeightedIntegralTools.md)
