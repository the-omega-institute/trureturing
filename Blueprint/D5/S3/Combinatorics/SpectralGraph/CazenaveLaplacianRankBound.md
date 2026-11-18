# Cazenave's Laplacian–rank inequality

## Abstract

The second largest ordinary Laplacian eigenvalue plus real adjacency rank is at most twice the edge count.

**Definition 1.1 (Conjecture 5 (#239534)).**

$$\operatorname{claim} = (\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n+2\right)\right),\; [\operatorname{DecidableRel}\left((G).\operatorname{Adj}\right)] (G).\operatorname{Connected} \Rightarrow \operatorname{LinWangCaiBroomSpectralRatio}.\operatorname{lapEig}\left(G, 1\right)+(((G).\operatorname{adjMatrix}\left(\mathrm{Real}\right)).\operatorname{rank} : \mathrm{Real}) \le 2 \cdot (((G).\operatorname{edgeFinset}).\operatorname{card} : \mathrm{Real}))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound.claim` (`✓ std3`).

*Citation.* Tristan Cazenave (2026). *Lemmas and Conjectures in Spectral Graph Theory*. URL: <https://arxiv.org/abs/2611.03879v1>.

*Commentary.*

Conjecture 5 of Lemmas and Conjectures in Spectral Graph Theory states that the second largest ordinary Laplacian eigenvalue plus adjacency rank is at most twice the number of edges. Section 1 fixes simple undirected connected graphs of order at least two, L = D − A and decreasing eigenvalues counted with multiplicity. Fin (n + 2) ranges over every permitted order. The adjacency matrix and its rank are over Real. The edgeFinset cardinality counts each unordered edge once. Decidable adjacency supplies instance data for the same graph.

**Theorem 1.2 (The unrestricted Laplacian–rank bound).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n+2\right)\right),\; [\operatorname{DecidableRel}\left((G).\operatorname{Adj}\right)] (G).\operatorname{Connected} \Rightarrow \operatorname{LinWangCaiBroomSpectralRatio}.\operatorname{lapEig}\left(G, 1\right)+(((G).\operatorname{adjMatrix}\left(\mathrm{Real}\right)).\operatorname{rank} : \mathrm{Real}) \le 2 \cdot (((G).\operatorname{edgeFinset}).\operatorname{card} : \mathrm{Real})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-cazenave2611c5` (proved) by `D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-cazenave2611c5","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tristan Cazenave (2026). *Lemmas and Conjectures in Spectral Graph Theory*. URL: <https://arxiv.org/abs/2611.03879v1>.

*Commentary.*

Positivity and decreasing order give twice the second eigenvalue at most the Laplacian trace, which is twice the edge count. Adjacency rank is at most graph order. These estimates settle graphs with at least as many edges as vertices, and the sparse branch when rank is below full rank. A remaining connected graph has one fewer edge than vertices and is a tree. At order two the smaller Laplacian eigenvalue is zero. At larger order, full adjacency rank forces an internal edge: otherwise two degree-one neighbours of a vertex of degree at least two have identical adjacency rows. Deleting an internal bridge partitions the vertices into two sides, each of size at least two. On the hyperplane where the endpoint coordinates agree, the bridge energy vanishes. Complete-side energy bounds give a Rayleigh upper bound equal to graph order minus two. A nonzero vector in the top-two spectral plane meets this hyperplane, and its Rayleigh lower bound gives the required second-eigenvalue estimate. All inequalities concern the same graph, vector and ordinary real Laplacian.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/CazenaveLaplacianRankBound.result`
- Dependency: [D5/S3/Combinatorics/Graph/Eccentric/DePatraCounting](../Graph/Eccentric/DePatraCounting.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/LinWangCaiBroomSpectralRatio](LinWangCaiBroomSpectralRatio.md)
