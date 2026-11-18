# Tree cuts, indegrees and local degree parity

## Abstract

Even indegrees and prescribed odd-degree vertices in finite trees.

A head function chooses one endpoint of each undirected edge. The indegree of a vertex counts edges choosing it. In a tree, the branches at a vertex are in bijection with its neighbors. Removing the edge to a neighbor identifies the side of the cut containing that neighbor with its branch after deleting the vertex.

**Theorem 1.1 (Which branches send an edge inward).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/TreeParity.even_indegrees_iff_odd_neighbor_branches`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/TreeParity.even_indegrees_iff_odd_neighbor_branches` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite tree of odd order and a head function choosing endpoints, all indegrees are even exactly when each neighbor edge points toward the designated vertex precisely when that neighbor's branch has odd order. Sum the indegrees on the branch side of the edge cut. Its internal tree edges number one less than its vertices, and only the cut edge can add a contribution.

**Theorem 1.2 (The even-indegree orientation).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/TreeParity.existsUnique_even_indegree_head`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/TreeParity.existsUnique_even_indegree_head` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite tree of odd order has a unique head function choosing endpoints and giving every vertex even indegree. The cut rule forces each head. The odd branches are even in number at every vertex, since their sizes sum to one less than the order of the tree.

**Theorem 1.3 (Realizing prescribed odd-degree vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/Incidence/TreeParity.exists_isTree_odd_neighborSet_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/TreeParity.exists_isTree_odd_neighborSet_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a finite vertex type, every nonempty even finite subset is the odd-degree set of a tree. Put two marked vertices at the ends of a path, all unmarked vertices in its interior, and the remaining marked vertices as leaves attached to one endpoint. Relabel this tree on the given type.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/TreeParity.even_indegrees_iff_odd_neighbor_branches`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/TreeParity.existsUnique_even_indegree_head`
- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/TreeParity.exists_isTree_odd_neighborSet_card`
