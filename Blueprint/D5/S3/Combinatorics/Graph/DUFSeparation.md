# Fifteen-vertex separation and the fourteen-vertex bound

## Abstract

Let H be a finite family of subsets of an n-element vertex type. Under DUF, complete blocks with different centers have at most one vertex in each side-intersection cell, and the four cells cannot all be occupied. Under the additional cap of at most four neighbors per ground pair, these blocks are whole link components and satisfy the center and component separation bounds. Three-uniformity is assumed only for the final counting bound.

**Theorem 1.1 (At most one vertex per intersection cell).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFSeparation.block_cell_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFSeparation.block_cell_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and complete blocks (c,A,S) and (d,C,D) in H with c distinct from d, A and C intersect in at most one vertex. Two shared vertices would place two large stars with different centers in one common link, where disjoint edges can be selected, contradicting DUF.

**Theorem 1.2 (At most three shared leaves).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFSeparation.block_support_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFSeparation.block_support_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and complete blocks (c,A,S) and (d,C,D) in H with c distinct from d, the supports A union S and C union D overlap in at most three vertices. Four nonempty side-intersection cells would give two disjoint diagonal edges in the common link of the centers.

**Theorem 1.3 (Centers cannot enter in both directions).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFSeparation.block_center_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFSeparation.block_center_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and the cap and complete blocks (c,A,S) and (d,C,D) in H with c distinct from d, if d belongs to A union S, then c does not belong to C union D and the two supports share at most two vertices. Saturation identifies opposite neighborhoods and excludes an entire side from the other component.

**Theorem 1.4 (The separation bound).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFSeparation.components_separated`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFSeparation.components_separated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and the cap, take two distinct members (c,U) and (d,W) of the center/support block set. The union of U with c included and W with d included has at least fifteen vertices. If c=d, the two component supports are disjoint and this union has exactly seventeen vertices.

**Theorem 1.5 (At most fourteen vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFSeparation.fourteen_vertex_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFSeparation.fourteen_vertex_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type of size at most fourteen and every actual three-uniform DUF family H with maximum pair codegree at most four, card(H)<=binom(n,2). Separation permits at most one exceptional component, and the exact counting identity then gives the bound. This is a restricted consequence, not a solution of the unrestricted problem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DUFSeparation.block_cell_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFSeparation.block_center_overlap`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFSeparation.block_support_overlap`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFSeparation.components_separated`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFSeparation.fourteen_vertex_bound`
- Dependency: [D5/S3/Combinatorics/Graph/DUFComponentCounts](DUFComponentCounts.md)
