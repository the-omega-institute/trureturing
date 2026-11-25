# The two fixed corner fibres

## Abstract

Normal form for a balanced nine-cube support under a leading swap

**Theorem 1.1 (One fixed corner fibre is empty).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedSwapNormalForm.exists_cubeMask_of_leadingSwap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedSwapNormalForm.exists_cubeMask_of_leadingSwap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The gauge for the pure transposition of the first two coordinates is −1 on the 00 fibre and +1 elsewhere. On a balanced support invariant under the swap, multiply this gauge by the switching signs at a vertex and its swapped vertex. The resulting sign is constant on each induced component.

On a nonempty preconnected support, this constant is the sign of the generator of the two-element swap group acting on the switching function. At a fixed vertex the switching signs square to 1. Occupied 00 and 11 fibres would then force the same sign to be both −1 and +1.

Complement both leading coordinates if 00 was omitted and use the identity otherwise. The omitted fibre becomes 11, the swap equates the two mixed fibres, and signed cube covariance preserves balance. The resulting support has slices (M, S, S, ∅) in order 00, 10, 01, 11.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedSwapNormalForm.exists_cubeMask_of_leadingSwap`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairBoundaryKernel](Q9PairBoundaryKernel.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
