# The Gram matrix of the signed boundary

## Abstract

Integral Gram identities for boundaries in the signed nine-cube

**Theorem 1.1 (Parity-restricted integral Gram and square determinant).**

$$KK^T = 9I-MM^T\quad \operatorname{det}\left(9I-MM^T\right) = \operatorname{det}\left(K_e\right)^2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.reduced_boundary_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a vertex set S, a parity b, and a finite row index type with decidable equality. Inject its indices into cube vertices of parity b. For any integer vertex signs of square one, let M and K be the corresponding switched Huang blocks on the opposite-parity columns inside and outside S, respectively.

Equal-parity entries vanish, so the full row Gram is entirely accounted for by opposite-parity columns. Splitting those columns yields the first equality. For every equivalence e from the row indices to the exterior column indices, K sub e is K with its columns reindexed by e. Its Gram is unchanged by reindexing, and multiplication and transposition of determinants give the second equality.

**Theorem 1.2 (Unsigned interior of a balanced support).**

$$KK^T = 9I-MM^T$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.balanced_boundary_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If S is Huang-balanced and the retained rows belong to S, an integer switching sign exists that makes M the ordinary biadjacency on the retained rows and selected opposite-parity columns.

On S the integer signs agree with the real balance witness. On each edge, the two endpoint signs cancel the original Huang sign, and nonedges have coefficient zero. The exterior block K uses the same switching function, so the determinant identity holds for every reindexing that makes K square.

**Theorem 1.3 (Square integral boundary after two deletions).**

$$ZZ^T = 9I-MM^T\quad \operatorname{det}\left(9I-MM^T\right) = \operatorname{det}\left(Z\right)^2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.cubic_reduced_boundary_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a balanced cubic induced subgraph of the nine-cube with 258 vertices. Delete two distinct selected vertices of the same parity. The two parity classes in S both have size 129 by counting the edges from either side. Each cube parity has 256 vertices, leaving 127 exterior columns opposite the 127 retained rows.

The factor Z uses a bijection from those rows to the opposite-parity exterior columns of the switched Huang matrix. M uses every selected column of the opposite parity and has ordinary unsigned adjacency entries.

**Theorem 1.4 (The separated 72- and 186-vertex supports).**

$$ZZ^T = 9I-MM^T\quad \operatorname{det}\left(9I-MM^T\right) = \operatorname{det}\left(Z\right)^2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.separated_cubic_boundary_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take disjoint Huang-balanced cubic induced supports of sizes 72 and 186 with no cube edge between them. Choose one vertex of each support in the same parity and delete those rows. The union is still cubic because its component neighborhoods are unchanged, and the two balance functions give one switching on its disjoint vertex sets.

The resulting signed exterior factor Z is square of order 127. The unsigned interior matrix M retains all selected columns of the opposite parity.

## Downstream application to spanning trees

The separated supports arise in Hong, Wu and Xia's Problem 2 on the nine-cube in Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, Section 7. The integral boundary argument revisits the previously recorded paper proof for this branch.

Two graph arguments connect the Lean factorization to spanning trees. First, ordering the rows and columns by support makes M block diagonal because there are no cross edges. The Gram defect is then the direct sum of the two reduced two-step Laplacians, one for each support after its row deletion.

Second, in each cubic bipartite support, eliminate the opposite-parity block 3I from the ordinary Laplacian cofactor at the deleted vertex. The two parity classes have equal size before deletion, so the cofactor equals three times the reduced two-step determinant. The matrix-tree theorem identifies that cofactor with the spanning-tree count.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.balanced_boundary_factorization`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.cubic_reduced_boundary_factorization`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.reduced_boundary_factorization`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryGram.separated_cubic_boundary_factorization`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound](../BalancedCubeLowerBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap](../HuangIntegralNormGap.md)
