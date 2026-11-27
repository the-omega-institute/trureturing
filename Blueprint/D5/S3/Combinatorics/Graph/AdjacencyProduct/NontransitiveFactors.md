# Non-vertex-transitive adjacency factors

## Abstract

The complete graph on 17 vertices has an ordinary integer adjacency-matrix factorization with both factors non-vertex-transitive.

**Theorem 1.1 (Two non-vertex-transitive factors of the complete graph).**

$$\exists H,K : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(17\right)\right), \operatorname{adjMatrix}\left(H, \mathbb{Z}\right) \operatorname{adjMatrix}\left(K, \mathbb{Z}\right) = \operatorname{Matrix.of}\left(1\right) - 1 \land \neg(\forall i,j: \operatorname{Fin}\left(17\right), \exists e: \operatorname{SimpleGraph.Iso}\left(H, H\right), e\left(i\right) = j) \land \neg(\forall i,j: \operatorname{Fin}\left(17\right), \exists e: \operatorname{SimpleGraph.Iso}\left(K, K\right), e\left(i\right) = j)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors.result` (`✓ std3`). ∎

*Resolves.* `Problems/akbari-elahimanesh-miraftab-nontransitive-adjacency-factors` (proved) by `D5/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"akbari-elahimanesh-miraftab-nontransitive-adjacency-factors","declaration_gid":"D5/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Saieed Akbari, Mohamad Parsa Elahimanesh and Bobby Miraftab (2025). *On Prime Matrix Product Factorizations*. DOI: [10.48550/arXiv.2512.24864](https://doi.org/10.48550/arXiv.2512.24864). URL: <https://arxiv.org/html/2512.24864v1#S5>.

*Commentary.*

In Section 5, item 2 of arXiv:2512.24864v1, Akbari, Elahimanesh and Miraftab ask for two non-transitive graphs H and K whose adjacency matrices B and C satisfy BC = J − I. The question is at https://arxiv.org/html/2512.24864v1#S5.I1.i2

The two graphs share the labelled vertex set Fin 17. They have decidable adjacency, and adjMatrix uses integer entries. Matrix.of(1) has every entry equal to one, the subtracted 1 is the identity, and the product is ordinary matrix multiplication.

The two graphs are defined by literal neighbor lists. The kernel checks symmetry, looplessness and the product entry at each ordered pair of vertices. Its value is zero on the diagonal and one off the diagonal.

Reindexing an adjacency matrix by a graph automorphism fixes the matrix and commutes with powers. The third power of B has diagonal entries 2 and 0 at vertices 0 and 1. The fourth power of C has diagonal entries 40 and 42 at vertices 0 and 2. These entries count walks that return to their starting vertex at the specified length. Each pair of differing entries rules out an automorphism between the corresponding vertices.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacencyProduct/NontransitiveFactors.result`
