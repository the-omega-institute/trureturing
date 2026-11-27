# Exact chordal reconstruction strata

## Abstract

Circumference determines the scalar reconstruction coefficient of a finite chordal graph. Finite modular tests, elimination orderings, root paths, and finite Hilbert centers give reconstruction laws in other targets.

**Theorem 1.1 (The scalar circumference formula).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.scalar_circumference_exact`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.scalar_circumference_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be finite and chordal, with a simple cycle of greatest length L. Orient each edge both ways with opposite real gains and suppose every triangle defect has absolute value at most one. There is a potential with every edge residual bounded by one minus two over L. A single gain assignment forces some edge residual at least that large for every potential.

Triangulation bounds the signed sum on any simple cycle of length l by l minus two in absolute value. Adding one minus two over L to each directed gain makes simple cycles and backtracks nonnegative. Repeated-vertex decomposition extends this to closed walks. Infima of directed walk costs give the potential inequalities. Along a longest cycle, unit gains along the path and minus one on its closing edge give the matching lower bound by telescoping.

**Theorem 1.2 (A finite test for universal abelian reconstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.finite_modulus_decides_abelian_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.finite_modulus_decides_abelian_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be finite, linearly ordered on vertices and chordal, and let T be a spanning tree contained in G. For a natural budget k and modulus q greater than three k plus one, a single cochain over the integers modulo q decides universal abelian feasibility. It assigns zero to tree edges and a separate signed coordinate to each edge outside the tree. Universal feasibility allows every additive abelian target and every set containing zero and the triangle defects. A potential uses sums of k elements of the allowed set as residuals.

Lift the modular residuals to short integer sums, choosing opposite lifts on opposite orientations. Every coordinate of a triangle discrepancy is a multiple of q with absolute value at most three k plus one, so it vanishes. The lifted residuals integrate to a potential by chordality. In any abelian target, first gauge the tree to zero, then send each integer basis element to the normalized gain of its edge.

**Theorem 1.3 (Bounded ancestor edges of a rooted tree).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_ancestor_banach_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_ancestor_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Root a tree at any vertex. Join two distinct vertices when one is on the root path of the other and their distance is at most the positive integer k. For skew gains in a real seminormed vector space with triangle defect at most epsilon, the displayed coefficient times epsilon bounds all edge residuals.

For each depth residue modulo k, integrate on the chain of marked ancestors and then along each branch to the vertex. Across one edge, at most one marked depth is crossed. The norm bound counts at most one triangle per endpoint, with no charge when that endpoint is marked. Each endpoint is marked in one residue class, and the average potential gives the claimed bound.

**Theorem 1.4 (Group reconstruction at clique number four).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_clique_four_group_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_clique_four_group_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite chordal graph have every clique of size at most four. Gains are inverted upon reversal in a group whose pseudometric is invariant under left and right multiplication. If every triangle defect is at most epsilon, the edge errors of one potential are at most twice epsilon.

In reverse simplicial elimination, record a two-factor residual on each edge and an ordering of each triangle with two controlled comparisons. The insertion rule supplies all three new triangle orderings and preserves the earlier ones.

**Theorem 1.5 (Group reconstruction at clique number five).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_clique_five_group_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_clique_five_group_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite chordal graphs with cliques of size at most five under the same group and gain assumptions, a potential gives edge errors at most three times epsilon.

Order each four-clique so that its successive path prefixes have budgets one, two, and one. The insertion rule propagates those budgets to all child faces. Available copies of an earlier neighbor fill out the frame for smaller separators.

**Theorem 1.6 (Closed walks factor through triangles).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.closed_walk_triangle_factors`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.closed_walk_triangle_factors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a closed walk p in a finite chordal graph and inverse-compatible gains in any group, its ordered gain is the ordered product of the factors in F. Each factor is a conjugate of the holonomy of an oriented triangle. Length subtraction is natural, so a trivial walk or a backtrack uses zero factors.

Rotate to a simplicial vertex in the induced support. Either delete a backtrack or close a triangle across its two neighbors. Conjugate the shorter factorization back to the original basepoint.

**Theorem 1.7 (Group reconstruction from a tree spanner).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_tree_spanner_approximate_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_tree_spanner_approximate_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose a spanning tree T of a finite chordal graph is contained in the graph and every graph edge has endpoints at tree distance at most t. The group and defect hypotheses are those of the clique bounds.

Integrate the gains on the tree. Closing a tree path with one graph edge gives a loop of length at most t plus one. Its triangle factors bound the residual by the displayed coefficient times the defect.

**Theorem 1.8 (Group reconstruction from graph radius).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_radius_approximate_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_radius_approximate_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the finite connected chordal graph have a vertex at distance at most r from every vertex. The same group and gain hypotheses apply. A potential integrates chosen shortest root walks, and each graph edge closes a loop of length at most two r plus one. The displayed coefficient times the defect bounds the residual.

**Theorem 1.9 (Hilbert reconstruction from finite Jung centers).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_hilbert_jung_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_hilbert_jung_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be finite and chordal with cliques of size at most k plus one, for k at least one. The target is any real inner product space. For skew gains whose triangle defects have norm at most epsilon, one potential bounds all edge residuals by the displayed coefficient times epsilon. J is the square root of the ratio of k minus one to twice k.

At each simplicial insertion, the candidate labels are at pairwise distance at most the sum of the old error bound and epsilon. A finite Jung center for at most k candidates shrinks that diameter by J. The displayed coefficient is the fixed point of this estimate.

**Theorem 1.10 (A finite-height clique-tree bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.cliqueTree_height_banach_gain_potential`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.cliqueTree_height_banach_gain_potential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the adjacent bags of a clique tree meet in at least one and at most q vertices, where q is at least two. If the tree has a root at distance at most h from every bag, every skew Banach gain assignment of defect at most epsilon admits a potential with the stated residual coefficient.

Distances through the root bound the clique-tree diameter by twice h. The center-extension recurrence begins at one and applies the separator averaging update. Solving this recurrence gives q minus one minus the product of q minus two and the h-th power of the ratio of q minus one to q.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.cliqueTree_height_banach_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.closed_walk_triangle_factors`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_ancestor_banach_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_clique_five_group_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_clique_four_group_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_hilbert_jung_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_radius_approximate_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.exists_tree_spanner_approximate_gain_potential`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.finite_modulus_decides_abelian_reconstruction`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata.scalar_circumference_exact`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential](../CliqueTreeBanachPotential.md)
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/EliminationForest](../EliminationForest.md)
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/GainPotential](../GainPotential.md)
