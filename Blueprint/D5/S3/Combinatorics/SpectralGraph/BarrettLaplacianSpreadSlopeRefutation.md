# No universal slope-one bound for digraph Laplacian spread

## Abstract

Independent clusters refute every universal slope-one Laplacian-spread bound.

An imbalanced five-vertex digraph has two zero-sum unit vectors with quadratic values 3408/679 and zero. Replacing each vertex by an independent cluster of size m produces an unweighted loopless digraph of order 5m whose spread is at least 3408m/679. The excess 13m/679 is unbounded.

**Definition 1.1 (The out-degree Laplacian).**

$$\forall n \in \operatorname{Nat},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{laplacian}\left(G\right) = \operatorname{Matrix}.\operatorname{diagonal}\left((\operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto \sum_{j : \operatorname{Fin}\left(n\right)} \operatorname{ite}\left(\operatorname{Digraph}.\operatorname{Adj}\left(G, i, j\right), 1, 0\right))\right) - \operatorname{Matrix}.\operatorname{of}\left((\operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{fun} (j : \operatorname{Fin}\left(n\right)) \mapsto \operatorname{ite}\left(\operatorname{Digraph}.\operatorname{Adj}\left(G, i, j\right), 1, 0\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.laplacian` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.1016/j.laa.2023.01.016](https://doi.org/10.1016/j.laa.2023.01.016). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2, states verbatim: “Moreover, we define the Laplacian matrix of Γ by L = D − A, where A is the adjacency matrix of Γ and D is a diagonal matrix whose ith diagonal entry is d⁺(i).” The same page states: “After indexing the vertex set as V = {1, 2, . . . , n}, we define the adjacency matrix of Γ by A = [aᵢⱼ]ⁿᵢ,ⱼ₌₁, where aᵢⱼ = 1 if (i, j) ∈ E and aᵢⱼ = 0 otherwise.” It also states: “We denote the out-degree of vertex i ∈ V by d⁺(i), which is equal to the number of edges of the form (i, j) ∈ E.” Fin n labels the vertices from zero; each arc contributes one to its source's row sum.

**Definition 1.2 (Restricted real quadratic values).**

$$\forall n \in \operatorname{Nat},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{quadraticValues}\left(G\right) = \{t : \operatorname{Real} \mid \exists x \in \operatorname{EuclideanSpace}\left(\operatorname{Real}, \operatorname{Fin}\left(n\right)\right),\; \sum_{i : \operatorname{Fin}\left(n\right)} x\left(i\right) = 0 \land \left(\Vert x\Vert = 1 \land t = \operatorname{dotProduct}\left((\operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto x\left(i\right)), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{laplacian}\left(G\right), (\operatorname{fun} (i : \operatorname{Fin}\left(n\right)) \mapsto x\left(i\right))\right)\right)\right)\}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.quadraticValues` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.1016/j.laa.2023.01.016](https://doi.org/10.1016/j.laa.2023.01.016). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2, defines the extrema by xᵀLx subject to x ⟂ e and ‖x‖ = 1, where e is the all ones vector. The formula gives precisely these values in the real Euclidean space. Coordinate sum zero expresses orthogonality to e; the norm is the Euclidean norm.

**Definition 1.3 (The lower extremum).**

$$\forall n \in \operatorname{Nat},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{alpha}\left(G\right) = \operatorname{sInf}\left(\operatorname{quadraticValues}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.alpha` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.1016/j.laa.2023.01.016](https://doi.org/10.1016/j.laa.2023.01.016). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2, states verbatim: “The algebraic connectivity of Γ is given by” α(Γ) = min{xᵀLx : x ⟂ e, ‖x‖ = 1}. The formula uses the infimum of that quadratic-value set; for order at least two the set is nonempty and compact, so the infimum is attained.

**Definition 1.4 (The upper extremum).**

$$\forall n \in \operatorname{Nat},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{beta}\left(G\right) = \operatorname{sSup}\left(\operatorname{quadraticValues}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.beta` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.1016/j.laa.2023.01.016](https://doi.org/10.1016/j.laa.2023.01.016). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2, states verbatim: “Another related and useful quantity is” β(Γ) = max{xᵀLx : x ⟂ e, ‖x‖ = 1}. The formula uses the supremum of the same set, attained for order at least two.

**Definition 1.5 (Laplacian spread).**

$$\forall n \in \operatorname{Nat},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{spread}\left(G\right) = \operatorname{beta}\left(G\right) - \operatorname{alpha}\left(G\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.spread` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.1016/j.laa.2023.01.016](https://doi.org/10.1016/j.laa.2023.01.016). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 3, page 5, states verbatim: “We define the Laplacian spread of a digraph Γ by” sp(Γ) = β(Γ) − α(Γ), “that is, sp(Γ) is equal to the length of the real part of Wᵣ(L).”

**Definition 1.6 (The slope-one conjecture).**

$$\operatorname{claim} = \left(\exists C \in \operatorname{Real},\; \forall n \in \operatorname{Nat},\; 2 \le n \Rightarrow \left(\forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \neg \operatorname{Digraph}.\operatorname{Adj}\left(G, i, i\right)\right) \Rightarrow \operatorname{spread}\left(G\right) \le (n : \operatorname{Real}) + C\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.claim` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.1016/j.laa.2023.01.016](https://doi.org/10.1016/j.laa.2023.01.016). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Conjecture 20 in the HTML rendering, numbered Conjecture 6.7 on page 16 of the arXiv v1 PDF, states verbatim: “The bound on the Laplacian spread of digraphs given in (3.2) can be reduced to a linear function in n with a slope of 1.” Section 6, page 14, states: “Note that all conjectures are made for unweighted digraphs.” Equation (3.2) on page 6 is sp(Γ) ≤ 5(n−1)/2. One real intercept must work for all n ≥ 2 and all loopless directed graphs; opposite arcs are allowed. The graph relation has no balance or polygonality assumption.

**Theorem 1.7 (Refutation for every real intercept).**

$$\neg (\exists C \in \operatorname{Real},\; \forall n \in \operatorname{Nat},\; 2 \le n \Rightarrow \left(\forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \neg \operatorname{Digraph}.\operatorname{Adj}\left(G, i, i\right)\right) \Rightarrow \operatorname{spread}\left(G\right) \le (n : \operatorname{Real}) + C\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-bce20` (refuted) by `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-bce20","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.1016/j.laa.2023.01.016](https://doi.org/10.1016/j.laa.2023.01.016). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

The Figure 3 graph has adjacency rows 00100, 10111, 11011, 00000 and 00000. The vectors (2,26,−26,−1,−1) and (0,0,0,1,−1) have coordinate sum zero, squared norms 1358 and 2, and Laplacian quadratic values 6816 and zero before normalization. Independent clusters multiply squared norms by m and quadratic values by m². Compact-sphere bounds compare the two normalized values with the supremum and infimum. Choosing a positive integer m > max(0,679C/13) gives spread > 5m + C. No calculation of every eigenvalue is required.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.alpha`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.beta`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.laplacian`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.quadraticValues`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.spread`
- Dependency: [D5/S1/Dynamics/Symbolic/FiniteGraphEntropy](../../../S1/Dynamics/Symbolic/FiniteGraphEntropy.md)
