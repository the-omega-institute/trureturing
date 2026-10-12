# The large cubic graph construction

## Abstract

Strict event counting supplies AR-labelings of large cubic graphs.

**Theorem 1.1 (An AR-labeling with the exact interval of labels).**

$$\operatorname{Cubic}\left(G\right) \land 12 \le \operatorname{EdgeCount}\left(G\right) \implies \operatorname{IsARGraph}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLarge.ar_graph_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite simple cubic graph having at least twelve edges, there is an AR-labeling onto the integer interval from one through the edge count. Choose a vertex v and two of its incident edges p and q, with opposite endpoints u and w. Simplicity makes v,u,w distinct. Give p and q the labels one and two. Enumerate every vertex's three incident edges, placing both marks first at v and the respective mark first at u and w. All other vertices have three free edges. The cardinalities of their additive collision events satisfy the four corresponding marked-event bounds. The cubic degree-sum identity supplies the arithmetic hypothesis making the sum of these bounds strictly smaller than the marked sample space. An outcome avoiding every collision is the required exact AR-labeling.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLarge.ar_graph_large`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphEvents](CubicARGraphEvents.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion](CubicARGraphUnion.md)
