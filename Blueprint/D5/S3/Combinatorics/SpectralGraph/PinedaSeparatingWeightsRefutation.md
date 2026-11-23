# Separating weights for three graph operators

## Abstract

Weighted paths obstruct each of the three universal separating-weight analogues.

Separation requires a separable characteristic polynomial, nonzero coordinates in every nonzero right eigenvector, and pairwise distinct coordinates in the specified modes. The nonzero-coordinate requirement includes the zero eigenspace. Weights are real and strictly positive on actual unordered edges or ordered arcs. Each support has its own polynomial and its own degree.

**Definition 1.1 (Normalized Laplacian analogue).**

$$\operatorname{NormalizedClaim} = (\forall n \in \operatorname{Nat},\; (2 \le n) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; (G.\operatorname{Connected}) \Rightarrow (\exists d \in \operatorname{Nat},\; \exists P \in \operatorname{MvPolynomial}\left(G.\operatorname{edgeSet}, \operatorname{Int}\right),\; P \ne 0 \land \left(P.\operatorname{IsHomogeneous}\left(d\right) \land \left(\forall w \in G.\operatorname{edgeSet} \to \operatorname{Real},\; (\operatorname{Positive}\left(w\right)) \Rightarrow (\operatorname{normalizedSep}\left(G, w\right) \Leftrightarrow \operatorname{MvPolynomial}.\operatorname{eval}_{2}\left((\operatorname{Int}.\operatorname{castRingHom}\left(\operatorname{Real}\right)), w, P\right) \ne 0)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.NormalizedClaim` (`✓ std3`).

*Citation.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

The operator is the symmetric normalized Laplacian I minus the adjacency matrix scaled on both sides by inverse square-root degrees. The eigenvectors are real. For the distinct-coordinate requirement the modes are orthogonal to the vector of square-root degrees.

**Definition 1.2 (Adjacency analogue).**

$$\operatorname{AdjacencyClaim} = (\forall n \in \operatorname{Nat},\; (2 \le n) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; (G.\operatorname{Connected}) \Rightarrow (\exists d \in \operatorname{Nat},\; \exists P \in \operatorname{MvPolynomial}\left(G.\operatorname{edgeSet}, \operatorname{Int}\right),\; P \ne 0 \land \left(P.\operatorname{IsHomogeneous}\left(d\right) \land \left(\forall w \in G.\operatorname{edgeSet} \to \operatorname{Real},\; (\operatorname{Positive}\left(w\right)) \Rightarrow (\operatorname{adjacencySep}\left(G, w\right) \Leftrightarrow \operatorname{MvPolynomial}.\operatorname{eval}_{2}\left((\operatorname{Int}.\operatorname{castRingHom}\left(\operatorname{Real}\right)), w, P\right) \ne 0)\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.AdjacencyClaim` (`✓ std3`).

*Citation.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

The symmetric weighted adjacency has one variable per edge and zero entries off the support. The eigenvectors are real. The distinct-coordinate requirement applies at eigenvalues strictly below the largest eigenvalue.

**Definition 1.3 (Directed Laplacian analogue).**

$$\operatorname{DirectedClaim} = (\forall n \in \operatorname{Nat},\; (2 \le n) \Rightarrow (\forall G \in \operatorname{Digraph}\left(\operatorname{Fin}\left(n\right)\right),\; (\forall i \in \operatorname{Fin}\left(n\right),\; \neg G.\operatorname{Adj}\left(i, i\right)) \Rightarrow ((\operatorname{HasSpanningOutArborescence}\left(G\right)) \Rightarrow (\exists d \in \operatorname{Nat},\; \exists P \in \operatorname{MvPolynomial}\left(\operatorname{Arc}\left(G\right), \operatorname{Int}\right),\; P \ne 0 \land \left(P.\operatorname{IsHomogeneous}\left(d\right) \land \left(\forall w \in \operatorname{Arc}\left(G\right) \to \operatorname{Real},\; (\operatorname{Positive}\left(w\right)) \Rightarrow (\operatorname{directedSep}\left(G, w\right) \Leftrightarrow \operatorname{MvPolynomial}.\operatorname{eval}_{2}\left((\operatorname{Int}.\operatorname{castRingHom}\left(\operatorname{Real}\right)), w, P\right) \ne 0)\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.DirectedClaim` (`✓ std3`).

*Citation.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

The loopless digraph contains a spanning out-arborescence. Rows receive arcs, so entry (i,j) of the adjacency reads the arc from j to i. The receiving-degree Laplacian is the diagonal row-sum matrix minus that adjacency. The eigenvectors are complex and the distinct-coordinate requirement applies at nonzero eigenvalues.

**Definition 1.4 (Question 7.5).**

$$\operatorname{claim} = (\operatorname{NormalizedClaim} \lor \left(\operatorname{AdjacencyClaim} \lor \operatorname{DirectedClaim}\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.claim` (`✓ std3`).

*Citation.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

An affirmative answer to any of the three universal analogues would imply this disjunction.

**Theorem 1.5 (The normalized Laplacian obstruction).**

$$\neg \operatorname{NormalizedClaim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.normalized_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

The five-vertex path has consecutive weights a, b, c, d and row degrees a, a+b, b+c, c+d, d. Scale the coordinates of (bd, 0, −ad, 0, ac) by the square roots of these degrees. The resulting nonzero vector is an eigenvector at 1 and vanishes at vertices 1 and 3, indexed from zero.

**Theorem 1.6 (The adjacency obstruction).**

$$\neg \operatorname{AdjacencyClaim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.adjacency_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

On the same path the weighted adjacency annihilates the nonzero vector (bd, 0, −ad, 0, ac). The zero coordinates at vertices 1 and 3 violate separation for every positive weighting.

**Theorem 1.7 (The receiving-degree Laplacian obstruction).**

$$\neg \operatorname{DirectedClaim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.directed_refuted` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

The out-path on vertices 0, 1, 2 has arcs 0 to 1 and 1 to 2, of weights p and q. The receiving-degree Laplacian has rows (0,0,0), (−p,p,0), (0,−q,q). Its last coordinate vector is a right eigenvector at q and its first two coordinates vanish.

**Theorem 1.8 (Refutation of the three analogues).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

On each of the indicated supports the nonvanishing implication would force the polynomial to vanish on the whole positive orthant. The real polynomial identity theorem on the product of positive intervals and the injective integer coefficient map force the original polynomial to be zero. This argument applies at every degree and uses only the nonzero-coordinate requirement.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.AdjacencyClaim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.DirectedClaim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.NormalizedClaim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.adjacency_refuted`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.directed_refuted`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.normalized_refuted`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation](AlbrightKemenyEdgeDerivativeRefutation.md)
