# Global Hilbert gain reconstruction below the Jung threshold

## Abstract

Every finite chordal graph admits Hilbert gain reconstruction at radius 241361 over 100000 times the triangle-defect budget. A diagonal term in the same estimate gives a uniform improvement for every finite clique cutoff.

**Theorem 1.1 (The global Hilbert reconstruction bound).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_sub_jung`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_sub_jung` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite chordal graph and skew gains in a real inner product space, one vertex potential bounds the norm of every edge residual by 241361 over 100000 times the common nonnegative triangle-defect budget. This constant is strictly below 2414 over 1000, which is strictly below one plus the square root of two. The gap from one plus the square root of two exceeds 3 over 5000.

Normalize positive defects to one and insert vertices in reverse perfect elimination order. The earlier neighbors of each new vertex form a clique. Preserve the edge cap and a triangle inequality whose right side is a weighted sum of deficits in squared edge norms and whose left side depends on the oldest edge's inner product with the triangle curl.

The new constraints are singleton and pair averages of squared distances with fixed offsets. Maximizing their minimum weighted value over the probability simplex gives a common center whenever all mixtures have nonpositive minimum. The variance identity divides the loss in each mixture into a diagonal term, old-edge deficits, new-curl deficits, row-mean energy, and centered energy.

For a new pair row, the curl alignment on the earlier clique splits into a mean and a centered fluctuation. Charge the companion deficits and fluctuations to the suffix beginning at the later pair endpoint. The decreasing scalar envelope integrates the remaining charge. The rational quadratic certificates at the interpolation nodes bound the envelope on the whole interval. Older triangles with small curl alignment supply a second deficit bound by weighting prefixes with a degree-four polynomial. The two estimates account for the centered energy and leave a credit of at least 57 over 10 times the sum of the squared vertex weights.

An empty predecessor clique imposes no rows. At defect budget zero the existing exact integration theorem gives the potential.

**Theorem 1.2 (The uniform finite-clique improvement).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_clique_credit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_clique_credit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every clique has at most N plus one vertices, with N a positive integer, the potential has an edge bound given by the square root of the global squared radius minus 57 over 10N, times the defect budget. This radius is at most the global radius minus 59 over 50N.

The new vertex and its predecessor clique together have at most N plus one vertices, so each probability vector in the insertion argument has at most N entries. Cauchy–Schwarz bounds their squared sum below by 1 over N. Add the resulting credit to each normalized row and use the same triangle invariant. Squaring the nonnegative linear radius proves the second comparison.

**Theorem 1.3 (The retained-curl bounds at three clique cutoffs).**

Lean statement: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_retained_curl`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_retained_curl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For clique cutoffs 31, 51, and 101, the radius factors are respectively 22302 over 10000, 22913 over 10000, and 23434 over 10000. Each conclusion supplies one potential for all edges and holds for any nonnegative triangle-defect budget.

At a simplicial insertion, maintain a lower bound on the sum of the edge deficits and the squared fixed triangle curls in every smaller clique. Subset rows supply the exact additional terms for each clique containing the new vertex. Product-weighted averaging of the old inequalities charges edges and triangles using symmetric polynomials on the complementary vertices.

Pair averaging bounds those symmetric polynomials by their uniform values and controls their loss away from uniform by the squared variation in the weights. The weighted Hilbert projection identity then bounds the new mixture minimum. An exact quadratic comparison for each cutoff closes the subset rows, including weights that vanish.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_clique_credit`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_retained_curl`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/HilbertGlobalSubJung.exists_hilbert_gain_potential_sub_jung`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/EliminationForest](../EliminationForest.md)
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/GainPotential](../GainPotential.md)
