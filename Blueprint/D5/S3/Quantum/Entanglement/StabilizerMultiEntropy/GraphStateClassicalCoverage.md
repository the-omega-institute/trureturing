# Integer orders and exact graph-state classical coverage

## Abstract

Graph-state generalized concentratable entanglement has a universal classical hit-probability representation exactly at integer orders above one.

**Theorem 1.1 (Universal classical hit law iff integer order).**

$$\forall K \in \mathbb{R},\; (1 < K) \Rightarrow ((\forall N \in \mathbb{N},\; \forall A \in \operatorname{SimpleBinaryAdjacency}\left(\operatorname{Fin}\left(N\right)\right),\; \exists p \in \operatorname{ProbabilityOnBinaryWords}\left(\operatorname{Fin}\left(N\right)\right),\; \forall S \in \operatorname{Subsets}\left(\operatorname{Fin}\left(N\right)\right),\; \operatorname{D}\left(K, A, S\right) = \operatorname{Hit}\left(S, p\right)) \Leftrightarrow (\exists n \in \mathbb{N},\; K = n + 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateClassicalCoverage.physical_graph_coverage_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Xiaoyu Liu, Johannes Knörzer, Zherui Jerry Wang, Jordi Tura (2025). *Generalized Concentratable Entanglement via Parallelized Permutation Tests*. DOI: [10.1103/jtlj-qs3y](https://doi.org/10.1103/jtlj-qs3y). URL: <https://arxiv.org/abs/2406.18517v1>.

*Commentary.*

A graph is any symmetric binary adjacency matrix with zero diagonal, including the graph on zero sites. The deficiency D(K,A,S) is one minus the arithmetic mean of the actual real power traces over the subsets of S, using the normalized reduced graph-state matrices. Equivalently it is (K - 1) times the GCE of S. A law p is nonnegative and normalized on binary words; Hit(S,p) is its mass on words nonzero on some site of S. One and the same law must work for all subsets S of the chosen graph.

At order n + 1, sample n independent induced vertex subsets uniformly, form each induced graph's odd-degree set, and XOR those sets. Its exact linear-cut Fourier moments give the desired law. For a noninteger order, a binary projective incidence graph makes a signed marginal negative through the exact projective rank product. The theorem concerns universality over graph states. It does not say that every graph at a noninteger order fails.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateClassicalCoverage.physical_graph_coverage_iff`
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/BinaryProjectiveRankPolynomial](BinaryProjectiveRankPolynomial.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/GraphStateConcentratableEntanglement](GraphStateConcentratableEntanglement.md)
