# Parity of descending edges in the nine-cube

## Abstract

Parity of descending edges in the nine-cube

**Theorem 1.1 (The total of the odd projected double fibres is even).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity.even_sum_doubleFibres_true`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity.even_sum_doubleFibres_true` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reduction of the full Huang eigenvector equation modulo two identifies the parity of each neighbor count with membership. Every two-step descent has two possible intermediate vertices. This pairs the mixed terms and forces the total on odd projected fibres to be even.

**Theorem 1.2 (Nine axes cannot each have a thirteen-to-one split).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity.not_all_axes_split_thirteen_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity.not_all_axes_split_thirteen_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Either orientation of this split contributes an odd summand. Nine such summands violate the congruence, excluding the size-84 branch after the local size reductions. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity.even_sum_doubleFibres_true`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity.not_all_axes_split_thirteen_one`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity](Q9OccupiedFibreParity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap](../HuangIntegralNormGap.md)
