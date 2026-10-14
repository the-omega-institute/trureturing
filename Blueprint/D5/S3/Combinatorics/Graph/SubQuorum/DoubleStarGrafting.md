# Double-star grafting on arbitrary finite graphs

## Abstract

Attaching a six-vertex double star at each vertex of any nonempty finite simple graph adds four vertices per gadget to the dissociation maximum and gives exactly five sub-quorum colors per base vertex.

**Definition 1.1 (The seven slots).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.localAdj`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.localAdj` (`✓ std3`).

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

The slots 0,1,2,3,4,5,6 are h,u,v,a,b,c,d. The undirected local edges are ha,uv,ua,ub,vc,vd. Thus u,v are the centers, and a,b,c,d are leaves of the six-vertex double star. Only h is an original vertex.

**Definition 1.2 (Keep every original edge).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.graftGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.graftGraph` (`✓ std3`).

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

For every vertex type V and simple graph F on V, the grafted graph has carrier V times Fin 7. Two slot-zero vertices are adjacent precisely when their base vertices are adjacent in F. Local edges occur only within the same base fiber. Each original vertex is attached to its designated leaf a. The construction makes no regularity, connectivity or bipartiteness assumption on F and has seven times the number of base vertices.

**Definition 1.3 (Actual partial support).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.coloredSupport`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.coloredSupport` (`✓ std3`).

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

For every finite set S and coloring c into Option C, the colored support consists exactly of vertices in S whose value differs from none. The empty support is allowed and represents no colors.

**Definition 1.4 (Count the represented image).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.palette`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.palette` (`✓ std3`).

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

The palette is the image of the colored support under c. It contains only some-values, so an unused color label is never counted and none is never a color. The map to this actual image is automatically onto. Color labels may belong to an arbitrary type with decidable equality.

**Definition 1.5 (Colored closed neighborhoods).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.goodAt`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.goodAt` (`✓ std3`).

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

At a colored vertex v with neighbor set N, twice the sum of one and the number of neighbors carrying c(v) is at least one plus the number of colored neighbors. The added one counts v itself once on each side. Uncolored neighbors do not enter either count. An uncolored v imposes no condition.

**Definition 1.6 (The graph condition).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.IsSubQuorum`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.IsSubQuorum` (`✓ std3`).

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

For every finite vertex type, simple graph and Option coloring, require goodAt at every vertex with its actual graph neighbor set. This is the same weak-majority convention as the source definition and the repository's hypercube partial-coloring predicate, with the support represented by Option values and surjectivity supplied by the actual palette.

**Definition 1.7 (The bounded maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.psiSq`

*Formalization.* `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.psiSq` (`✓ std3`).

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

For every finite graph, maximize the cardinality of the actual palette of an admissible Option Nat coloring, bounded by the number of vertices. Every finite palette can be relabeled by natural numbers, so the label carrier does not limit the parameter. The empty coloring attains zero. For a nonempty graph a one-vertex coloring attains one; on the nonempty grafted graphs the explicit construction attains five times the base size.

**Theorem 1.8 (Exact induced degree-at-most-one maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.beta_graftGraph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.beta_graftGraph` (`✓ std3`). ∎

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

For every finite nonempty V with decidable equality and every simple graph F with decidable adjacency, beta(graftGraph F,2)=4|V|+beta(F,2). The existing beta parameter maximizes cardinality over actual finsets whose selected vertices have fewer than two selected neighbors. Restrict any such set to the base and each gadget. A gadget contains at most four selected vertices: both centers exclude all leaves; one center permits at most one of its own leaves and both opposite leaves; with neither center only the four leaves remain. Conversely extend an optimal base set by u,b,c,d in every gadget. The selected local edges are ub and the attachment leaves a are absent, so the original induced degrees are preserved.

**Theorem 1.9 (Exact sub-quorum color maximum).**

Lean statement: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.psiSq_graftGraph`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.psiSq_graftGraph` (`✓ std3`). ∎

*Citation.* Wenlin Zhang (2026). *From hypercubes to grids: sub-quorum colorings and structural bounds*. URL: <https://github.com/the-omega-institute/subquorum-colorings/blob/8e42baefc9f4ea674c44023fee6385502839fb17/manuscript/paper.tex>.

*Commentary.*

For every finite nonempty V with decidable equality and every simple graph F, psiSq(graftGraph F)=5|V|. Leave every base vertex uncolored, give each gadget's two centers one shared color, and give its four leaves four separate colors. Distinct gadgets use distinct palettes. For the upper bound restrict any coloring to a base vertex together with its gadget. Only the centers and the attachment leaf are needed. Six represented colors would force all seven vertices colored. Each center must then have a same-color neighbor. Unless the centers share their color there are two distinct collisions, leaving at most five colors. If they share their color, the remaining vertices have distinct colors, and a sees two differently colored neighbors, u and h, violating majority. Thus each seven-vertex fiber has at most five colors. The global palette is the union of these fiber palettes and is bounded by their sum. This includes the source's accounting for base-exclusive colors: any extra base color forces a deficit in its gadget. Original edges within F are unrestricted. No grid, signed-matrix or Hall characterization is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.IsSubQuorum`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.beta_graftGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.coloredSupport`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.goodAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.graftGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.localAdj`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.palette`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.psiSq`
- Truth anchor: `D5/S3/Combinatorics/Graph/SubQuorum/DoubleStarGrafting.psiSq_graftGraph`
- Dependency: [D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation](../StarFormingDissociationRefutation.md)
