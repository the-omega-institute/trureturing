# No universal slope-one Laplacian-spread bound

## Abstract

The Laplacian spread of loopless unweighted digraphs admits no universal bound n + C.

**Definition 1.1 (Out-degree).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{outDegree}\left(G, i\right) = \sum_{j : \operatorname{Fin}\left(n\right)} \operatorname{Matrix}.\operatorname{map}\left(\operatorname{FiniteGraphEntropy}.\operatorname{adjacency}\left(\operatorname{Digraph}.\operatorname{Adj}\left(G\right)\right), (\operatorname{Nat}.\operatorname{cast} : \mathbb{N} \to \mathbb{R})\right)\left(i, j\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.outDegree` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2: "We denote the out-degree of vertex i∈V by d⁺(i), which is equal to the number of edges of the form (i,j)∈E." The sum counts the real 0/1 entries in the selected row. FiniteGraphEntropy.adjacency supplies the natural entries and Nat.cast embeds them into the reals.

**Definition 1.2 (In-degree).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{inDegree}\left(G, i\right) = \sum_{j : \operatorname{Fin}\left(n\right)} \operatorname{Matrix}.\operatorname{map}\left(\operatorname{FiniteGraphEntropy}.\operatorname{adjacency}\left(\operatorname{Digraph}.\operatorname{Adj}\left(G\right)\right), (\operatorname{Nat}.\operatorname{cast} : \mathbb{N} \to \mathbb{R})\right)\left(j, i\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.inDegree` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2: "Similarly, we denote the in-degree of vertex i∈V by d⁻(i), which is equal to the number of edges of the form (j,i)∈E." The sum counts the incoming arcs in the selected column.

**Definition 1.3 (Directed Laplacian matrix).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{laplacian}\left(G\right) = \operatorname{Matrix}.\operatorname{diagonal}\left(\operatorname{outDegree}\left(G\right)\right) - \operatorname{Matrix}.\operatorname{map}\left(\operatorname{FiniteGraphEntropy}.\operatorname{adjacency}\left(\operatorname{Digraph}.\operatorname{Adj}\left(G\right)\right), (\operatorname{Nat}.\operatorname{cast} : \mathbb{N} \to \mathbb{R})\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.laplacian` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2: "Moreover, we define the Laplacian matrix of Γ by L=D−A, where A is the adjacency matrix of Γ and D is a diagonal matrix whose ith diagonal entry is d⁺(i)." Both matrices have real entries indexed by Fin n.

**Definition 1.4 (Balance at every vertex).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Balanced}\left(G\right) \Leftrightarrow \left(\forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{outDegree}\left(G, i\right) = \operatorname{inDegree}\left(G, i\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.Balanced` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 4, page 9: "Now, let Γ=(V,E) be a balanced digraph, that is, d⁺(i)=d⁻(i) for all i∈V." Balance equates the outgoing and incoming degree at each vertex separately.

**Definition 1.5 (Zero-sum unit quadratic values).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{quadraticValues}\left(G\right) = \{t : \mathbb{R} | \exists x \in \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right),\; \sum_{i : \operatorname{Fin}\left(n\right)} x\left(i\right) = 0 \land \left(\Vert x \Vert = 1 \land t = \operatorname{dotProduct}\left((\operatorname{fun} i : \operatorname{Fin}\left(n\right) \mapsto x\left(i\right)), \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{laplacian}\left(G\right), (\operatorname{fun} i : \operatorname{Fin}\left(n\right) \mapsto x\left(i\right))\right)\right)\right)\}$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.quadraticValues` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2: "The algebraic connectivity of Γ is given by α(Γ) = min_{x⊥e, ‖x‖=1} xᵀLx." "Another related and useful quantity is β(Γ) = max_{x⊥e, ‖x‖=1} xᵀLx." This set is exactly those real quadratic values: the sum of the Euclidean coordinates is zero, the Euclidean norm is one, and the value is dotProduct x (Matrix.mulVec L x). It is nonempty for n≥2 and compact; the extrema are attained.

**Definition 1.6 (Minimum quadratic value).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{alpha}\left(G\right) = \operatorname{sInf}\left(\operatorname{quadraticValues}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.alpha` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2: "The algebraic connectivity of Γ is given by α(Γ) = min_{x⊥e, ‖x‖=1} xᵀLx." The infimum agrees with this minimum for n≥2, since the quadratic-value set is nonempty and compact.

**Definition 1.7 (Maximum quadratic value).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{beta}\left(G\right) = \operatorname{sSup}\left(\operatorname{quadraticValues}\left(G\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.beta` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 2, page 2: "Another related and useful quantity is β(Γ) = max_{x⊥e, ‖x‖=1} xᵀLx." The supremum agrees with this maximum for n≥2.

**Definition 1.8 (Laplacian spread).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{spread}\left(G\right) = \operatorname{beta}\left(G\right) - \operatorname{alpha}\left(G\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.spread` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Section 3, pages 4–5: "We define the Laplacian spread of a digraph Γ by sp(Γ) = β(Γ) − α(Γ), that is, sp(Γ) is equal to the length of the real part of Wᵣ(L)." The expression uses the same constrained real extrema as Section 2.

**Lemma 1.9 (Compactness of the quadratic-value set).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{IsCompact}\left(\operatorname{quadraticValues}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.quadraticValues_isCompact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

The zero-sum unit sphere is the intersection of a compact Euclidean sphere with a closed linear equation. Its continuous quadratic image is compact, including the empty cases at orders zero and one.

**Lemma 1.10 (Normalization gives a quadratic value).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \forall x \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; \sum_{i : \operatorname{Fin}\left(n\right)} x\left(i\right) = 0 \Rightarrow \left(x \ne 0 \Rightarrow \frac{\operatorname{dotProduct}\left(x, \operatorname{Matrix}.\operatorname{mulVec}\left(\operatorname{laplacian}\left(G\right), x\right)\right)}{\operatorname{dotProduct}\left(x, x\right)} \in \operatorname{quadraticValues}\left(G\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.rayleigh_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

A nonzero zero-sum vector can be divided by its Euclidean norm. The resulting unit vector has quadratic value equal to its Rayleigh quotient.

**Definition 1.11 (Conjecture 20).**

$$\operatorname{claim} \Leftrightarrow (\exists C \in \mathbb{R},\; \forall n \in \mathbb{N},\; 2 \le n \Rightarrow \left(\forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \neg (\operatorname{Digraph}.\operatorname{Adj}\left(G, i, i\right))\right) \Rightarrow \operatorname{spread}\left(G\right) \le (n : \mathbb{R}) + C\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.claim` (`✓ std3`).

*Citation.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

Conjecture 20, page 16: "The bound on the Laplacian spread of digraphs given in (5) can be reduced to a linear function in n with a slope of 1." The real constant C is independent of the order and the loopless unweighted digraph. Orders n≥2 are exactly those with a nonempty zero-sum unit sphere.

**Theorem 1.12 (Conjecture 20 is false).**

$$\neg (\exists C \in \mathbb{R},\; \forall n \in \mathbb{N},\; 2 \le n \Rightarrow \left(\forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall i \in \operatorname{Fin}\left(n\right),\; \neg (\operatorname{Digraph}.\operatorname{Adj}\left(G, i, i\right))\right) \Rightarrow \operatorname{spread}\left(G\right) \le (n : \mathbb{R}) + C\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Wayne Barrett; Thomas R. Cameron; Emily Evans; H. Tracy Hall; Mark Kempton (2022). *On the Laplacian spread of digraphs*. DOI: [10.48550/arXiv.2206.15410](https://doi.org/10.48550/arXiv.2206.15410). URL: <https://arxiv.org/abs/2206.15410v1>.

*Commentary.*

A five-vertex digraph has zero-sum vectors with Rayleigh values 3408/679 and 0. Replacing each vertex by m independent vertices multiplies both values by m. The order is 5m and the spread is at least (5+13/679)m, so no fixed intercept C can give a bound 5m+C for all positive m.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.Balanced`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.alpha`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.beta`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.inDegree`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.laplacian`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.outDegree`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.quadraticValues`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.quadraticValues_isCompact`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.rayleigh_mem`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.spread`
- Dependency: [D5/S1/Dynamics/Symbolic/FiniteGraphEntropy](../../../S1/Dynamics/Symbolic/FiniteGraphEntropy.md)
