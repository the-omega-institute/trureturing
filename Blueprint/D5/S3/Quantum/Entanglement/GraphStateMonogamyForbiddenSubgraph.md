# The forbidden-subgraph conjecture for MMI in graph states

## Abstract

Every graph state that violates monogamy of mutual information is carried by local complementations to a graph with an induced four-star, and that graph is a generalized star for the partition that places the three leaves of the star in their own parts and every other vertex in the centre. This proves the forbidden-subgraph conjecture of Fuentes, Keeler, Munizzi and Pollack for every number of qubits.

**Definition 1.1 (Local complementation).**

$$\operatorname{Adj}\left(\operatorname{lc}\left(G, v\right), a, b\right) \Leftrightarrow (a \ne b \land (\operatorname{Adj}\left(G, a, b\right) \Leftrightarrow (\neg (\operatorname{Adj}\left(G, v, a\right) \land \operatorname{Adj}\left(G, v, b\right)))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lc` (`✓ std3`).

*Citation.* Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack (2025). *Monogamy of Mutual Information in Graph States*. DOI: [10.48550/arXiv.2511.19585](https://doi.org/10.48550/arXiv.2511.19585). URL: <https://arxiv.org/abs/2511.19585v1>.

*Commentary.*

Local complementation at v complements the adjacency between any two neighbours of v and keeps every other adjacency; on graph states it realizes the local Clifford operations.

**Definition 1.2 (LC equivalence).**

$$(\operatorname{lcSeq}\left(G, \operatorname{nil}\right) = G) \land (\operatorname{lcSeq}\left(G, \operatorname{cons}\left(v, s\right)\right) = \operatorname{lcSeq}\left(\operatorname{lc}\left(G, v\right), s\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lcSeq` (`✓ std3`).

*Citation.* Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack (2025). *Monogamy of Mutual Information in Graph States*. DOI: [10.48550/arXiv.2511.19585](https://doi.org/10.48550/arXiv.2511.19585). URL: <https://arxiv.org/abs/2511.19585v1>.

*Commentary.*

lcSeq(G, s) applies local complementation at the vertices of the list s, first to last; H is LC-equivalent to G when H = lcSeq(G, s) for some list s.

**Definition 1.3 (Induced four-star).**

$$\operatorname{IsClaw}\left(G, c, i, j, k\right) \Leftrightarrow (\operatorname{Adj}\left(G, c, i\right) \land \left(\operatorname{Adj}\left(G, c, j\right) \land \left(\operatorname{Adj}\left(G, c, k\right) \land \left(i \ne j \land \left(i \ne k \land \left(j \ne k \land \left(\left(\neg (\operatorname{Adj}\left(G, i, j\right))\right) \land \left(\left(\neg (\operatorname{Adj}\left(G, i, k\right))\right) \land \left(\neg (\operatorname{Adj}\left(G, j, k\right))\right)\right)\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.IsClaw` (`✓ std3`).

*Citation.* Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack (2025). *Monogamy of Mutual Information in Graph States*. DOI: [10.48550/arXiv.2511.19585](https://doi.org/10.48550/arXiv.2511.19585). URL: <https://arxiv.org/abs/2511.19585v1>.

*Commentary.*

The vertex c is adjacent to three distinct vertices i, j, k that are pairwise non-adjacent, so c, i, j, k induce the four-vertex star that the paper denotes K_4.

**Definition 1.4 (Entanglement entropy of a graph state).**

$$\forall M \in \operatorname{Matrix}\left(A, \operatorname{compl}\left(A\right), \operatorname{ZMod}\left(2\right)\right),\; (\forall x \in A,\; \forall y \in \operatorname{compl}\left(A\right),\; M\left(x, y\right) = \operatorname{if} \operatorname{Adj}\left(G, x, y\right) \operatorname{then} 1 \operatorname{else} 0) \Rightarrow (\operatorname{entropy}\left(G, A\right) = \operatorname{rank}\left(M\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.entropy` (`✓ std3`).

*Citation.* Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack (2025). *Monogamy of Mutual Information in Graph States*. DOI: [10.48550/arXiv.2511.19585](https://doi.org/10.48550/arXiv.2511.19585). URL: <https://arxiv.org/abs/2511.19585v1>.

*Commentary.*

The entropy of a set A of qubits in the graph state of G is the rank of the adjacency block of A: every matrix M over Z_2 with rows indexed by A and columns by the complement of A whose entry at x, y is 1 when x and y are adjacent and 0 otherwise has rank S(G, A).

**Definition 1.5 (Violation of MMI).**

$$\operatorname{ViolatesMMI}\left(G\right) \Leftrightarrow (\exists I \in \operatorname{Finset}\left(V\right),\; \exists J \in \operatorname{Finset}\left(V\right),\; \exists K \in \operatorname{Finset}\left(V\right),\; \left(\operatorname{Disjoint}\left(I, J\right) \land \left(\operatorname{Disjoint}\left(I, K\right) \land \operatorname{Disjoint}\left(J, K\right)\right)\right) \land \operatorname{entropy}\left(G, \operatorname{union}\left(I, J\right)\right) + \operatorname{entropy}\left(G, \operatorname{union}\left(I, K\right)\right) + \operatorname{entropy}\left(G, \operatorname{union}\left(J, K\right)\right) < \operatorname{entropy}\left(G, I\right) + \operatorname{entropy}\left(G, J\right) + \operatorname{entropy}\left(G, K\right) + \operatorname{entropy}\left(G, \operatorname{union}\left(\operatorname{union}\left(I, J\right), K\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.ViolatesMMI` (`✓ std3`).

*Citation.* Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack (2025). *Monogamy of Mutual Information in Graph States*. DOI: [10.48550/arXiv.2511.19585](https://doi.org/10.48550/arXiv.2511.19585). URL: <https://arxiv.org/abs/2511.19585v1>.

*Commentary.*

The graph state violates an instance of monogamy of mutual information: pairwise disjoint sets I, J, K with S(I ∪ J) + S(I ∪ K) + S(J ∪ K) less than S(I) + S(J) + S(K) + S(I ∪ J ∪ K).

**Definition 1.6 (Generalized star).**

$$\operatorname{IsGeneralizedStar}\left(H, C, P\right) \Leftrightarrow (\left(\forall p \in \operatorname{Fin}\left(k\right),\; \operatorname{Nonempty}\left(\operatorname{P}\left(p\right)\right)\right) \land \left(\left(\forall p \in \operatorname{Fin}\left(k\right),\; \forall q \in \operatorname{Fin}\left(k\right),\; p \ne q \Rightarrow (\operatorname{Disjoint}\left(\operatorname{P}\left(p\right), \operatorname{P}\left(q\right)\right))\right) \land \left(\left(\forall p \in \operatorname{Fin}\left(k\right),\; \operatorname{Disjoint}\left(C, \operatorname{P}\left(p\right)\right)\right) \land \left(\operatorname{union}\left(C, \operatorname{biUnion}\left(\operatorname{univ}, P\right)\right) = \operatorname{univ} \land \left(\left(\forall p \in \operatorname{Fin}\left(k\right),\; \forall q \in \operatorname{Fin}\left(k\right),\; p \ne q \Rightarrow ((\forall x \in \operatorname{P}\left(p\right),\; \forall y \in \operatorname{P}\left(q\right),\; \neg (\operatorname{Adj}\left(H, x, y\right))))\right) \land \left(\forall p \in \operatorname{Fin}\left(k\right),\; \exists x \in \operatorname{P}\left(p\right),\; \exists z \in C,\; \operatorname{Adj}\left(H, x, z\right)\right)\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.IsGeneralizedStar` (`✓ std3`).

*Citation.* Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack (2025). *Monogamy of Mutual Information in Graph States*. DOI: [10.48550/arXiv.2511.19585](https://doi.org/10.48550/arXiv.2511.19585). URL: <https://arxiv.org/abs/2511.19585v1>.

*Commentary.*

H is a generalized star with centre C and parts P_1, ..., P_k: the parts are nonempty and pairwise disjoint, the centre is disjoint from every part, the centre and the parts cover all vertices (univ), no edge joins two different parts, and every part has a vertex adjacent to a vertex of the centre.

**Definition 1.7 (The forbidden-subgraph conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{ViolatesMMI}\left(G\right) \Rightarrow (\exists s \in \operatorname{List}\left(\operatorname{Fin}\left(n\right)\right),\; \exists c \in \operatorname{Fin}\left(n\right),\; \exists i \in \operatorname{Fin}\left(n\right),\; \exists j \in \operatorname{Fin}\left(n\right),\; \exists k \in \operatorname{Fin}\left(n\right),\; \operatorname{IsClaw}\left(\operatorname{lcSeq}\left(G, s\right), c, i, j, k\right) \land \operatorname{IsGeneralizedStar}\left(\operatorname{lcSeq}\left(G, s\right), \operatorname{sdiff}\left(\operatorname{univ}, \{i,j,k\}\right), (\{i\},\{j\},\{k\})\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.claim` (`✓ std3`).

*Citation.* Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack (2025). *Monogamy of Mutual Information in Graph States*. DOI: [10.48550/arXiv.2511.19585](https://doi.org/10.48550/arXiv.2511.19585). URL: <https://arxiv.org/abs/2511.19585v1>.

*Commentary.*

For every number n of qubits and every graph G on the vertices 0, ..., n - 1 whose graph state violates MMI, some graph H = lcSeq(G, s) has an induced four-star c; i, j, k, and H is a generalized star with centre univ \ {i, j, k}, the vertices other than i, j, k, and parts {i}, {j}, {k}.

**Theorem 1.8 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.result` (`✓ std3`). ∎

*Resolves.* `Problems/fuentes-2025-mmi-forbidden-subgraph` (proved) by `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"fuentes-2025-mmi-forbidden-subgraph","declaration_gid":"D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jesus Fuentes, Cynthia Keeler, William Munizzi, Jason Pollack (2025). *Monogamy of Mutual Information in Graph States*. DOI: [10.48550/arXiv.2511.19585](https://doi.org/10.48550/arXiv.2511.19585). URL: <https://arxiv.org/abs/2511.19585v1>.

*Commentary.*

Local complementation at a vertex of a vertex set commutes with restriction to that set, so an induced four-star or a relabelled graph reached on part of the vertices lifts to the whole graph. A connected graph has an ordering of its vertices in which each vertex after the first is adjacent to an earlier one; the graph on the first m + 1 vertices is that on the first m with a new vertex adjacent to a nonempty set T, which local complementation at earlier vertices keeps nonempty. For the representatives K_1, K_2, the path on three vertices, the path 1 - 2 - 3 - 0, the 5-cycle 0 - 1 - 3 - 4 - 2 - 0 and the triangular prism with triangles 012, 345 and matching 03, 14, 25, and every nonempty T, a listed sequence of at most three local complementations carries the extension to a graph with an induced four-star or to a relabelling of the next representative, and every extension of the prism reaches an induced four-star; these 120 certificates are checked by evaluation. So a connected graph reaching no induced four-star has at most six vertices and is carried to a relabelled representative. Local complementation at v changes the adjacency block of A by the row operation 1 + u e_v^T (u_v = 0) when v is in A, an involution over Z_2, and the entropy of A equals that of its complement, so no entropy changes; relabelling permutes rows and columns. A vertex set without edges to its complement makes every adjacency block block-diagonal, so entropies add over components. The representatives satisfy MMI: for K_1, K_2, the 3-path, the 5-cycle and the prism a parity criterion makes the rows of every set of at most half the vertices independent, so the entropy of A is min(|A|, n - |A|) and MMI reduces to arithmetic; for the 4-path a violation needs four nonempty parts, hence single vertices, and the three pairs have entropies at least 2, 2 and 1. By induction on the number of vertices, a graph state reaching no induced four-star therefore satisfies MMI. Conversely, given an induced four-star c; i, j, k, the leaves are pairwise non-adjacent and adjacent to c, which lies in the centre, so the partition is a generalized star.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.IsClaw`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.IsGeneralizedStar`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.ViolatesMMI`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.entropy`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lc`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.lcSeq`
- Truth anchor: `D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.result`
