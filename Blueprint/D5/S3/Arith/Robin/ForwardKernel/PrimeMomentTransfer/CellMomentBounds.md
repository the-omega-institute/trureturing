# Cell moment bounds

## Abstract

Cell sampling bounds connect discrete second and fourth moments with the fixed unit sampling interval.

**Theorem 1.1 (Unit interval probability).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.unit_dyadic_probability`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.unit_dyadic_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lebesgue measure restricted to the interval [1,2] is a probability measure.

**Theorem 1.2 (Uniform pointwise bounds).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.normalized_crude_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.normalized_crude_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For N at least two, log N at least one, H and M at least one, and MH at most N, the normalized discrete increments are bounded by 4(M+1)sqrt(H log N) for natural n with floor(N)<=n<=ceil(2N). On [1,2], the continuous increments have the same bound plus (2 log(4N)+2)/sqrt(H log N), uniformly in 0<=a<=b<=M.

**Theorem 1.3 (Fourth integrability on one sampling space).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.sampling_memLp`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.sampling_memLp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same size and endpoint conditions, both t mapped to Z(H,a,b,Nt,N) and t mapped to S(H,a,b,floor(Nt))/sqrt(H log N) belong to L4 for Lebesgue measure restricted to [1,2].

**Theorem 1.4 (Uniform cell second moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.uniform_cell_second`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.uniform_cell_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume singular-series values one on the empty set and singletons, MeanSquareHL(3,SS,beta) and the interval correlation input, with 0<alpha<beta<1/3 and M>=1. There is C>=1 such that eventually the second integral of the normalized floor sampled increment on [1,2] is at most C uniformly over natural H between N^alpha and N^beta and all 0<=a<=b<=M. The same cell quadrature estimate applies to second and fourth powers; this second bound uses only the quadratic arithmetic transfer.

**Theorem 1.5 (Uniform cell fourth moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.uniform_cell_fourth`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.uniform_cell_fourth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume singular-series values one on the empty set and singletons, MeanSquareHL4(SS,beta) and the interval correlation bounds, with 0<alpha<beta<1/4 and M>=1. There is a constant C>=1 such that, for all sufficiently large N, the fourth integral of the normalized floor sampled increment on [1,2] is at most C, uniformly in natural H between N^alpha and N^beta and 0<=a<=b<=M.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.normalized_crude_bounds`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.sampling_memLp`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.uniform_cell_fourth`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.uniform_cell_second`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellMomentBounds.unit_dyadic_probability`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CellQuadrature](CellQuadrature.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ContinuousSampling](ContinuousSampling.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights](CutoffWeights.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteFourthBound](DiscreteFourthBound.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteSecondBound](DiscreteSecondBound.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra](NormalizationAlgebra.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/UniformRates](UniformRates.md)
