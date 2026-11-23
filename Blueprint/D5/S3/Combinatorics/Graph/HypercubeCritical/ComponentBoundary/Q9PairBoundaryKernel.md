# Eliminating the empty slice

## Abstract

Two-axis reduction of weighted Huang boundary kernels

**Definition 1.1 (The two-slice kernel of the nine-cube action).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairBoundaryKernel.weightedBoundaryKernelEquiv`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairBoundaryKernel.weightedBoundaryKernelEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Order the blocks by their leading bits as 00, 10, 01, 11. The allowed source blocks are M, S, S, and the empty set. The allowed image blocks are independently M', S', S', and the empty set. A boundary kernel consists of functions supported on the source mask whose weighted Huang images are supported on the image mask.

Let a and b be the leading weights, let B be the weighted action of the seven remaining axes, and put c = a² + b². Over a field with c nonzero, the empty source block forces f11 = 0. The empty image block then forces b f10 + a f01 = 0. Thus p = f00 and q = (a f10 - b f01) / c recover the source as (p, a q, -b q, 0).

In these coordinates the weighted Huang action sends (p, q) to (B p + c q, -B q + p). The lift preserves and reflects the paired masks on both sides, giving a linear equivalence of the two boundary kernels.

If the field contains r with r² = c, rescale q to r q. The action in the rescaled coordinates is the weighted Huang action with a single leading axis of weight r. The positive B slice has leading bit true.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairBoundaryKernel.weightedBoundaryKernelEquiv`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9WeightedStarLift](Q9WeightedStarLift.md)
