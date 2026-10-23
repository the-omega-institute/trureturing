# The star bound for the least-energy uniform overlap fails

## Abstract

A triangulated complete graph refutes the proposed star bound for the uniform overlap of the least adjacency eigenspace.

The vertex set is Fin n, and G is a simple graph with decidable adjacency. The bracket denotes the instance argument for decidable adjacency; this argument is implicit in the matrix and overlap expressions. SimpleGraph.adjMatrix G real is the real adjacency matrix. Named objects retain their Lean namespaces.

**Definition 1.1 (The least adjacency eigenvalue).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], \operatorname{let} (hA: \operatorname{Matrix.IsHermitian}\left(\operatorname{SimpleGraph.adjMatrix}\left(G, \mathbb{R}\right)\right)) := (\operatorname{Iff.mpr}\left(\operatorname{Matrix.{{isHermitian}_{iff}}_{isSymm}}, \operatorname{SimpleGraph.{isSymm}_{adjMatrix}}\left(G\right)\right)); (\operatorname{D5.S3.Quantum.Dynamics.QuantumBatteryUniformOverlapRefutation.lamMin}\left(G\right) = \operatorname{iInf}\left(\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\operatorname{Matrix.IsHermitian.eigenvalues}\left(hA, i\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.lamMin` (`✓ std3`).

*Citation.* Matthieu Sarkis, Oskar A. Prośniak, Samuel Nigro, Alexandre Tkatchenko (2026). *Star Topology Optimizes the Charging Power of Quantum Batteries*. DOI: [10.48550/arXiv.2603.10853](https://doi.org/10.48550/arXiv.2603.10853). URL: <https://arxiv.org/abs/2603.10853v1>.

*Commentary.*

The real adjacency matrix is symmetric, hence Hermitian. The local hA is its Hermitian proof, obtained from SimpleGraph.isSymm_adjMatrix by Matrix.isHermitian_iff_isSymm. Matrix.IsHermitian.eigenvalues hA enumerates its real eigenvalues on Fin n. Their infimum in the real numbers defines lamMin, with every natural n included. For n greater than zero this is the least adjacency eigenvalue in the diagonalization of Section III.A, equation (11).

**Definition 1.2 (The overlap of the least eigenspace).**

$$\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], \operatorname{D5.S3.Quantum.Dynamics.QuantumBatteryUniformOverlapRefutation.wmin}\left(G\right) = \sum_{(i: \operatorname{Fin}\left(n\right))} (\sum_{(j: \operatorname{Fin}\left(n\right))} (\operatorname{D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum.idempotent}\left(G, \operatorname{D5.S3.Quantum.Dynamics.QuantumBatteryUniformOverlapRefutation.lamMin}\left(G\right), i, j\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.wmin` (`✓ std3`).

*Citation.* Matthieu Sarkis, Oskar A. Prośniak, Samuel Nigro, Alexandre Tkatchenko (2026). *Star Topology Optimizes the Charging Power of Quantum Batteries*. DOI: [10.48550/arXiv.2603.10853](https://doi.org/10.48550/arXiv.2603.10853). URL: <https://arxiv.org/abs/2603.10853v1>.

*Commentary.*

Section III.A, equation (11), defines the mode weights as the squares of the inner products of the all-ones vector with the orthonormal adjacency eigenvectors. For a graph with at least one edge, N and its edge count M are positive, so E_k(h) = (N/M) epsilon_k + h in equation (14) is increasing in epsilon_k. Thus the minimizing modes in Section III.C are exactly the least-eigenvalue eigenvectors. D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum.idempotent G (lamMin G) is the orthogonal projection onto their eigenspace. Summing all its entries gives the squared norm of the projection of the all-ones vector, including every vector in a repeated least eigenspace.

**Definition 1.3 (Conjecture 1 on all graphs with an edge).**

$$(\operatorname{D5.S3.Quantum.Dynamics.QuantumBatteryUniformOverlapRefutation.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], (\operatorname{Set.Nonempty}\left(\operatorname{SimpleGraph.edgeSet}\left(G\right)\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Dynamics.QuantumBatteryUniformOverlapRefutation.wmin}\left(G\right) \le \frac{(n: \mathbb{R})}{2} - \operatorname{Real.sqrt}\left((n: \mathbb{R}) - 1\right)))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.claim` (`✓ std3`).

*Citation.* Matthieu Sarkis, Oskar A. Prośniak, Samuel Nigro, Alexandre Tkatchenko (2026). *Star Topology Optimizes the Charging Power of Quantum Batteries*. DOI: [10.48550/arXiv.2603.10853](https://doi.org/10.48550/arXiv.2603.10853). URL: <https://arxiv.org/abs/2603.10853v1>.

*Commentary.*

Sarkis, Prosniak, Nigro and Tkatchenko, Section III.C, Conjecture 1, equation (24), propose the displayed inequality for every non-empty graph on n vertices. Non-empty means that the edge set has an element. Every natural n, every simple graph on Fin n, and every decidable adjacency are quantified. Observation 2, equation (23), gives the right-hand side as the least-energy uniform overlap of the star graph.

**Theorem 1.4 (A triangulated complete graph contradicts the bound).**

$$\neg (\operatorname{D5.S3.Quantum.Dynamics.QuantumBatteryUniformOverlapRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sarkis-prosniak-nigro-tkatchenko-2026-uniform-overlap-refutation` (refuted) by `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sarkis-prosniak-nigro-tkatchenko-2026-uniform-overlap-refutation","declaration_gid":"D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Matthieu Sarkis, Oskar A. Prośniak, Samuel Nigro, Alexandre Tkatchenko (2026). *Star Topology Optimizes the Charging Power of Quantum Batteries*. DOI: [10.48550/arXiv.2603.10853](https://doi.org/10.48550/arXiv.2603.10853). URL: <https://arxiv.org/abs/2603.10853v1>.

*Commentary.*

Take the q-triangulation of the complete graph on ten core vertices, with q = 27: for each of its 45 edges, add 27 vertices adjacent to precisely the two endpoints. The resulting graph has 10 + 27 times 45 = 1225 vertices and has an edge. Let A be its real adjacency matrix. The vector v with value 1 on each core vertex and -1/9 on each attached vertex satisfies A v = -18 v.

For every real vector x on these vertices, completing squares at each attached vertex gives x^T (A + 18 I) x at least 5 times the sum of the squared core coordinates minus one half of the square of their sum. Cauchy-Schwarz makes this nonnegative. Hence every adjacency eigenvalue is at least -18, and v shows that -18 is the least eigenvalue.

The sum of the coordinates of v is -125 and its squared norm is 25. Since v lies in the least eigenspace, Cauchy-Schwarz bounds its uniform overlap from below by (-125)^2/25 = 625. But 625 > 1225/2 - sqrt(1224), contradicting Conjecture 1.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.lamMin`
- Truth anchor: `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.result`
- Truth anchor: `D5/S3/Quantum/Dynamics/QuantumBatteryUniformOverlapRefutation.wmin`
- Dependency: [D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum](AverageMixingTraceMaximum.md)
- Dependency: [D5/S3/Quantum/Dynamics/LaplacianPeakTransferTrees](LaplacianPeakTransferTrees.md)
