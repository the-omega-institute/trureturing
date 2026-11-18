# Odd spanning trees of line graphs

## Abstract

Odd line-graph spanning trees are characterized by odd branches of an endpoint split tree.

The root graph is finite, undirected and simple. Its line graph has the root edges as vertices. A spanning tree is connected and acyclic on that entire vertex type, hence has a nonempty vertex set.

**Theorem 1.1 (The endpoint partition criterion).**

$$\forall (V : Type), [\operatorname{Finite}\left(V\right)], \forall (F : \operatorname{SimpleGraph}\left(V\right)), (\exists (H : \operatorname{SimpleGraph}\left(\operatorname{E}\left(F\right)\right)), (H \le \operatorname{L}\left(F\right)) \land ((\operatorname{IsTree}\left(H\right)) \land (\forall (e : \operatorname{E}\left(F\right)), \operatorname{Odd}\left(\lvert \operatorname{N}\left(H, e\right) \rvert\right)))) \Leftrightarrow ((0 < \lvert \operatorname{E}\left(F\right) \rvert) \land ((\operatorname{Even}\left(\lvert \operatorname{E}\left(F\right) \rvert\right)) \land (\exists (P : \operatorname{EndpointPartition}\left(F\right)), (\operatorname{IsTree}\left(\operatorname{T}\left(P\right)\right)) \land (\forall (b : \operatorname{Block}\left(P\right)), (2 \le \lvert \operatorname{N}\left(\operatorname{T}\left(P\right), b\right) \rvert) \Rightarrow (2 \le \lvert \{ C : \operatorname{Components}\left(\operatorname{T}\left(P\right) - b\right) \mid \operatorname{Odd}\left(\lvert \operatorname{supp}\left(C\right) \rvert\right) \} \rvert)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.result` (`✓ std3`). ∎

*Resolves.* `Problems/zheng-wu-2025-odd-line-spanning-trees` (proved) by `D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zheng-wu-2025-odd-line-spanning-trees","declaration_gid":"D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jingyu Zheng and Baoyindureng Wu (2025). *Odd spanning trees of a graph*. URL: <https://arxiv.org/abs/2503.17676v1>.

*Commentary.*

A partition P assigns nonempty classes of incident edges at each root vertex. A class bears its root vertex as a tag. T(P) joins the classes of each root edge at its two endpoints, one edge per root edge. An isolated root vertex contributes no classes. A branch at b is a connected component of the induced graph on all vertices of T(P) other than b, and its order is the cardinality of its support.

The equivalence holds for disconnected roots and roots with isolates. Both sides fail when the root edge count is zero or odd. The two-odd-branch requirement applies exactly at vertices of T(P) with at least two neighbors.

In the forward direction, restrict the spanning tree to the incident edges at each root vertex. The connected components of the resulting forests define the blocks. Each line-tree edge belongs to a unique forest. The block graph is connected, and subtracting the local tree sizes shows that a block graph with m edges has m + 1 vertices.

The sum of the degrees contributed by the two endpoint blocks to each line-tree vertex is odd. Orient its root edge toward the block making the odd contribution. Each local tree has an even number of odd-degree vertices, so every block has even indegree. The cut count identifies the incoming edges with the odd-order branches. A local tree on at least two vertices has at least two odd-degree vertices.

Conversely, the odd branches specify the even-indegree orientation of T(P). At each block choose a tree with exactly its incoming members of odd degree. A singleton uses the one-vertex tree. For larger blocks the incoming set is nonempty and even, and a path with leaves attached realizes the prescribed set. Join the local trees on their original edge labels. The union is connected, has m − 1 edges, and gives every original edge exactly one odd local contribution.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.result`
- Dependency: [D5/S3/Combinatorics/Graph/Incidence/EndpointSplit](EndpointSplit.md)
- Dependency: [D5/S3/Combinatorics/Graph/Incidence/TreeParity](TreeParity.md)
