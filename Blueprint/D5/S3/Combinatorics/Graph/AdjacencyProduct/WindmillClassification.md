# Adjacency-matrix factorization of windmill graphs

## Abstract

A windmill admits an ordinary product of two simple graph adjacency matrices over the integers exactly when it has one blade and its blade order is one modulo four.

**Definition 1.1 (Windmill graph).**

Lean statement: `D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.windmill`

*Formalization.* `D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.windmill` (`✓ std3`).

*Citation.* Saieed Akbari, Mohamad Parsa Elahimanesh and Bobby Miraftab (2025). *On Prime Matrix Product Factorizations*. DOI: [10.48550/arXiv.2512.24864](https://doi.org/10.48550/arXiv.2512.24864). URL: <https://arxiv.org/html/2512.24864v1#S5>.

*Commentary.*

The vertex set is Option (Fin d × Fin (t − 1)). The none vertex is the hub and is adjacent to every blade vertex. Two blade vertices are adjacent exactly when their first coordinates agree and their second coordinates differ. The graph is loopless.

**Theorem 1.2 (Which windmills factor).**

$$\forall d,t \in \mathbb{N}, 1 \leq d \land 3 \leq t \implies ((\exists B,C : \operatorname{SimpleGraph}\left(\operatorname{Option}\left(\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(t-1\right)\right)\right), \operatorname{A}\left(B\right) \operatorname{A}\left(C\right) = \operatorname{A}\left(\operatorname{windmill}\left(d, t\right)\right)) \iff (d = 1 \land t \equiv 1 \pmod{4}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.result` (`✓ std3`). ∎

*Resolves.* `Problems/akbari-elahimanesh-miraftab-windmill-factorization` (proved) by `D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"akbari-elahimanesh-miraftab-windmill-factorization","declaration_gid":"D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Saieed Akbari, Mohamad Parsa Elahimanesh and Bobby Miraftab (2025). *On Prime Matrix Product Factorizations*. DOI: [10.48550/arXiv.2512.24864](https://doi.org/10.48550/arXiv.2512.24864). URL: <https://arxiv.org/html/2512.24864v1#S5>.

*Commentary.*

In Section 5, item 1 of arXiv:2512.24864v1, Akbari, Elahimanesh and Miraftab ask which pairs (d, t) give a windmill that admits a factorization. The question is at https://arxiv.org/html/2512.24864v1#S5.I1.i1

The quantifier ranges over all pairs of simple undirected graphs on the windmill's labelled vertex set. The notation A(G) denotes the integer adjacency matrix of G, and juxtaposition denotes ordinary matrix multiplication.

Symmetry reverses the product and makes both factors commute with the windmill adjacency matrix. The product at a blade vertex and the hub supplies a non-hub intermediate neighbor. Commutation at that entry then forces each factor to join the hub to every blade. Distinct blades would therefore give a positive product entry at a nonedge.

A single blade is a complete graph. Commutation gives constant degrees for the two factors, whose product is t − 1. The second factor induces a graph of degree one on the first factor's neighbors of any vertex. The degree-sum formula gives even degree for the first factor, and reversing the factors gives even degree for the second. For t = 4k + 1 the cyclic steps of the first factor are ±1. Those of the second factor are 4j + 2 and 4j + 3 for 0 ≤ j < k. The sums partition the nonzero residues into blocks of four, with one representation per residue.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/AdjacencyProduct/WindmillClassification.windmill`
