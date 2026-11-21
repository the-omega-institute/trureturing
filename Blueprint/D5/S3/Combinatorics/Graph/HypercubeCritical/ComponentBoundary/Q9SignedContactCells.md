# The separated cubic supports

## Abstract

Signed contact cancellation in the nine-cube

Hong, Wu and Xia's Problem 2 asks whether the nine-cube has a 258-point induced support of maximum degree three. Consider the candidate consisting of two separated components. https://arxiv.org/html/2610.09483v1#Thmproblem2 Take disjoint connected Huang-balanced cubic induced supports C and D of sizes 72 and 186 with no cube edge between them. Fix a cube parity b. Let f and g be their switching vectors extended by zero and restricted to b. For axes i and j, write A(x) for f(x) times the signed double flip of g by ΓᵢΓⱼ at x.

**Theorem 1.1 (Signed contacts cancel on each parity).**

$$\sum_{x} A(x) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells.signed_overlap_parity_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Give axis j weight t and every other axis weight one. The resulting Huang operator squares to (8 + t²)I. The crossing map sends the 129 selected vertices on parity b to the 127 exterior vertices on the opposite parity. On its kernel, the C and D images are orthogonal. Their interior supports are disjoint by separation and their exterior images are negatives of each other. The sum of exterior squares therefore vanishes and each image stays on its own support.

Pair the D part with Γᵢ applied to the fixed C switch f. The weighted image stays on D, so separation makes the pairing zero. At unit weights the anticommutator and the switching eigen-equation also make it zero. Their difference is t − 1 times the signed overlap functional L, which consequently vanishes on the crossing kernel for t ≠ 1.

Append evaluation at one C vertex of parity b and the row L. Rank-nullity leaves a nonzero zero-vector for these rows and the crossing whenever t ≠ 1. The augmented matrix has order 129 and its determinant is continuous, so it is singular at t = 1. Each component part at unit weights lifts to a supported eigenvector of eigenvalue 3 by adding one third of its Huang image. The edge identity and connectedness make that eigenvector a multiple of the component switch. The root evaluation kills the C multiple, leaving a nonzero D multiple on which L vanishes.

**Theorem 1.2 (For distinct axes, signed contacts cancel in every two-bit cell).**

$$\sum_{x : x_i=p, x_j=q} A(x) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells.signed_overlap_cell_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct i and j, multiply the C switch by either bit character or by their product. Conjugation negates the weights on the character's axes and preserves the supported eigen-equation. The weighted anticommutator on C and separation on D then give the vanishing overlap against each nonconstant character. Probe with an axis whose other axis has changed sign. A diagonal term vanishes by disjointness because Γᵢ² = I.

The parity result supplies the constant coefficient. The indicator of a fixed pair of bits p and q is one quarter of the product of the two corresponding character factors, so its expansion uses precisely these four zero coefficients.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells.signed_overlap_cell_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells.signed_overlap_parity_zero`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary](../BalancedCubeComponentBoundary.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram](Q9BoundaryGram.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang](Q9IsotropicHuang.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenSaturation](../SupportedEigenSaturation.md)
