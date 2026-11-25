# The bipartition under weight-preserving symmetries

## Abstract

The bipartition at an irrational Perron value with rational square

**Theorem 1.1 (A weight-preserving permutation preserves each color class).**

Lean statement: `D5/S3/Combinatorics/Graph/PerronFrobenius/IrrationalQuadraticBipartition.preserves_bipartition_of_sq_rat`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PerronFrobenius/IrrationalQuadraticBipartition.preserves_bipartition_of_sq_rat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite bipartite graph have symmetric nonnegative rational weights and be connected through its positive-weight edges. Suppose a strictly positive vector has eigenvalue ρ, where ρ is irrational and ρ² is rational. Every permutation preserving the weight matrix preserves the two color classes.

The permutation fixes the positive vector by the maximum ratio argument. Adding the two translated matrices to the original matrix gives a symmetric rational matrix with the same positive vector at eigenvalue 3ρ. Its rational characteristic polynomial also has the root −3ρ. The two eigenvectors force the ratio of their entries to alternate in sign along every positive edge. Connectivity propagates a nonzero ratio to every vertex. Replacing the last edge of a path to the permuted vertex would produce an odd closed walk if the permutation changed its color.

For Hong, Wu and Xia’s Problem 2, suppose a connected cubic support in Q9 has unsigned weighted adjacency with Perron value equal to the Euclidean weight norm for every positive coordinate weighting. If an affine cube symmetry stabilizing that support has a proper nonempty invariant set I of axes, use weight 2 on I and 1 elsewhere. The squared norm is 9 + 3|I|, which lies strictly between 9 and 36 and is divisible by 3, hence is not a square. If the axis action is a single 9-cycle, a parity-changing stabilizer has a parity-changing ninth power with trivial axis action. This translation falls under the first case with a singleton I. These cases exclude parity-changing stabilizers under the stated weighted saturation assumption. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PerronFrobenius/IrrationalQuadraticBipartition.preserves_bipartition_of_sq_rat`
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Irreducible](MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Irreducible.md)
- Dependency: [D5/S3/Combinatorics/Graph/PerronFrobenius/MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Lemmas](MCMCSupplier/LinearAlgebra/Matrix/PerronFrobenius/Lemmas.md)
