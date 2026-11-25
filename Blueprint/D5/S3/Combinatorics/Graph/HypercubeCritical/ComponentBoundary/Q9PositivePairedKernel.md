# Positive kernels on occupied fibre components

## Abstract

Positive kernels on occupied fibre components

**Theorem 1.1 (Absolute values preserve a complementary Gram kernel).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.abs_mem_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.abs_mem_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the occupied matrix is entrywise nonnegative and its Gram plus the empty Gram is scalar, replacing a kernel vector by its absolute value preserves the kernel. This follows from the fixed squared norm and the increased occupied quadratic form.

**Theorem 1.2 (One occupied component works for every weight).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.exists_fixed_occupiedComponent_emptyFibre_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.exists_fixed_occupiedComponent_emptyFibre_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupied graph decomposes the complementary Gram into blocks. Polynomial determinant factorization selects a single universally singular block. For positive transverse weights the kernel can be chosen with the switching signs, and every coefficient on that block is nonzero.

**Theorem 1.3 (Two actual components with fixed kernel blocks).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.exists_two_components_with_fixed_occupied_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.exists_two_components_with_fixed_occupied_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal weighted singularity of two actual components forces each dominant axis to have a fixed occupied block carrying a boundary kernel for every real weighting. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.abs_mem_kernel`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.exists_fixed_occupiedComponent_emptyFibre_kernel`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel.exists_two_components_with_fixed_occupied_kernel`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary](../CoordinateHalves/Q9DominantAxisBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance](../HuangCubeCovariance.md)
