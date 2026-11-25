# Separating weights for three graph operators

## Abstract

Weighted paths obstruct each of the three universal separating-weight analogues.

Separation requires a separable characteristic polynomial, nonzero coordinates in every nonzero right eigenvector, and pairwise distinct coordinates in the specified modes. The nonzero-coordinate requirement includes the zero eigenspace. Weights are real and strictly positive on actual unordered edges or ordered arcs. Each support has its own polynomial and its own degree.

**Definition 1.1 (Normalized Laplacian analogue).**

$$\operatorname{NormalizedClaim} = (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\begin{aligned}&\operatorname{let} V := \operatorname{Fin}\left(n\right) \operatorname{in}\\&\forall G \in \operatorname{SimpleGraph}\left(V\right),\; (G.\operatorname{Connected}) \Rightarrow (\begin{aligned}&\operatorname{let} E := G.\operatorname{edgeSet} \operatorname{in}\\&\exists d \in \mathbb{N},\; \exists P \in \operatorname{MvPolynomial}\left(E, \mathbb{Z}\right),\; \begin{aligned}&P \ne 0 \land P.\operatorname{IsHomogeneous}\left(d\right) \land\\&\forall w \in E \to \mathbb{R},\; \begin{aligned}&(\forall e \in E,\; 0 < w\left(e\right)) \Rightarrow\\&((\begin{aligned}&\operatorname{let} A := [\operatorname{if} G.\operatorname{Adj}\left(i, j\right) \operatorname{then} w\left(s\left(i, j\right)\right) \operatorname{else} 0]_{i,j \in V} \operatorname{in}\\&\begin{aligned}&\operatorname{let} h := i \mapsto \sqrt{\sum_{j \in V} A\left(i, j\right)} \operatorname{in}\\&\begin{aligned}&\operatorname{let} M := I - [\frac{A\left(i, j\right)}{h\left(i\right) \cdot h\left(j\right)}]_{i,j \in V} \operatorname{in}\\&\begin{aligned}&\operatorname{Separable}\left(\operatorname{charpoly}\left(M\right)\right)\\&\land (\forall lambda \in \mathbb{R},\; \forall x \in V \to \mathbb{R},\; (x \ne 0 \land M \cdot x = lambda \cdot x) \Rightarrow (\forall i \in V,\; x\left(i\right) \ne 0))\\&\land (\forall lambda \in \mathbb{R},\; \forall x \in V \to \mathbb{R},\; (x \ne 0 \land M \cdot x = lambda \cdot x) \Rightarrow ((\sum_{i \in V} h\left(i\right) \cdot x\left(i\right) = 0) \Rightarrow (\operatorname{Injective}\left(x\right))))\end{aligned}\end{aligned}\end{aligned}\end{aligned}) \Leftrightarrow \operatorname{MvPolynomial}.\operatorname{eval}_{2}\left((\operatorname{Int}.\operatorname{castRingHom}\left(\mathbb{R}\right)), w, P\right) \ne 0)\end{aligned}\end{aligned}\end{aligned})\end{aligned}))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.NormalizedClaim` (`✓ std3`).

*Citation.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

The operator is the symmetric normalized Laplacian I minus the adjacency matrix scaled on both sides by inverse square-root degrees. The symbol s(i,j) denotes the unordered pair in the edge subtype when i and j are adjacent. The eigenvectors are real. For the distinct-coordinate requirement the modes are orthogonal to the vector of square-root degrees.

**Definition 1.2 (Adjacency analogue).**

$$\operatorname{AdjacencyClaim} = (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\begin{aligned}&\operatorname{let} V := \operatorname{Fin}\left(n\right) \operatorname{in}\\&\forall G \in \operatorname{SimpleGraph}\left(V\right),\; (G.\operatorname{Connected}) \Rightarrow (\begin{aligned}&\operatorname{let} E := G.\operatorname{edgeSet} \operatorname{in}\\&\exists d \in \mathbb{N},\; \exists P \in \operatorname{MvPolynomial}\left(E, \mathbb{Z}\right),\; \begin{aligned}&P \ne 0 \land P.\operatorname{IsHomogeneous}\left(d\right) \land\\&\forall w \in E \to \mathbb{R},\; \begin{aligned}&(\forall e \in E,\; 0 < w\left(e\right)) \Rightarrow\\&((\begin{aligned}&\operatorname{let} A := [\operatorname{if} G.\operatorname{Adj}\left(i, j\right) \operatorname{then} w\left(s\left(i, j\right)\right) \operatorname{else} 0]_{i,j \in V} \operatorname{in}\\&\begin{aligned}&\operatorname{Separable}\left(\operatorname{charpoly}\left(A\right)\right)\\&\land (\forall lambda \in \mathbb{R},\; \forall x \in V \to \mathbb{R},\; (x \ne 0 \land A \cdot x = lambda \cdot x) \Rightarrow (\forall i \in V,\; x\left(i\right) \ne 0))\\&\land (\forall lambda \in \mathbb{R},\; \forall x \in V \to \mathbb{R},\; (x \ne 0 \land A \cdot x = lambda \cdot x) \Rightarrow ((\exists mu \in \mathbb{R},\; \operatorname{HasEigenvalue}\left(A, mu\right) \land lambda < mu) \Rightarrow (\operatorname{Injective}\left(x\right))))\end{aligned}\end{aligned}) \Leftrightarrow \operatorname{MvPolynomial}.\operatorname{eval}_{2}\left((\operatorname{Int}.\operatorname{castRingHom}\left(\mathbb{R}\right)), w, P\right) \ne 0)\end{aligned}\end{aligned}\end{aligned})\end{aligned}))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.AdjacencyClaim` (`✓ std3`).

*Citation.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

The symmetric weighted adjacency has one variable per unordered edge and zero entries off the support. The symbol s(i,j) denotes the unordered pair in the edge subtype when i and j are adjacent. The eigenvectors are real. The distinct-coordinate requirement applies when the adjacency has a strictly larger eigenvalue.

**Definition 1.3 (Directed Laplacian analogue).**

$$\operatorname{DirectedClaim} = (\forall n \in \mathbb{N},\; (2 \le n) \Rightarrow (\begin{aligned}&\operatorname{let} V := \operatorname{Fin}\left(n\right) \operatorname{in}\\&\forall G \in \operatorname{Digraph}\left(V\right),\; (\forall i \in V,\; \neg G.\operatorname{Adj}\left(i, i\right)) \Rightarrow (\begin{aligned}&(\exists T \in \operatorname{Digraph}\left(V\right),\; \begin{aligned}&T \le G \land\\&\exists r \in V,\; \forall v \in V,\; \exists p \in \left(\operatorname{Path}_{T}\right)\left(r, v\right),\; \forall q \in \left(\operatorname{Path}_{T}\right)\left(r, v\right),\; q = p\end{aligned}) \Rightarrow\\&\begin{aligned}&\operatorname{let} E := \left\{(i,j) \in V \times V \mid G.\operatorname{Adj}\left(i, j\right)\right\} \operatorname{in}\\&\exists d \in \mathbb{N},\; \exists P \in \operatorname{MvPolynomial}\left(E, \mathbb{Z}\right),\; \begin{aligned}&P \ne 0 \land P.\operatorname{IsHomogeneous}\left(d\right) \land\\&\forall w \in E \to \mathbb{R},\; \begin{aligned}&(\forall e \in E,\; 0 < w\left(e\right)) \Rightarrow\\&((\begin{aligned}&\operatorname{let} A := [\operatorname{if} G.\operatorname{Adj}\left(j, i\right) \operatorname{then} w\left((j,i)\right) \operatorname{else} 0]_{i,j \in V} \operatorname{in}\\&\begin{aligned}&\operatorname{let} M := \operatorname{Complexify}\left(\operatorname{diag}\left(i \mapsto \sum_{j \in V} A\left(i, j\right)\right) - A\right) \operatorname{in}\\&\begin{aligned}&\operatorname{Separable}\left(\operatorname{charpoly}\left(M\right)\right)\\&\land (\forall lambda \in \mathbb{C},\; \forall x \in V \to \mathbb{C},\; (x \ne 0 \land M \cdot x = lambda \cdot x) \Rightarrow (\forall i \in V,\; x\left(i\right) \ne 0))\\&\land (\forall lambda \in \mathbb{C},\; \forall x \in V \to \mathbb{C},\; (x \ne 0 \land M \cdot x = lambda \cdot x) \Rightarrow ((lambda \ne 0) \Rightarrow (\operatorname{Injective}\left(x\right))))\end{aligned}\end{aligned}\end{aligned}) \Leftrightarrow \operatorname{MvPolynomial}.\operatorname{eval}_{2}\left((\operatorname{Int}.\operatorname{castRingHom}\left(\mathbb{R}\right)), w, P\right) \ne 0)\end{aligned}\end{aligned}\end{aligned}\end{aligned})\end{aligned}))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.DirectedClaim` (`✓ std3`).

*Citation.* Santiago Pineda Montoya, Edisson Gallego González, Jaiberth Porras Barrera, Johan Heriberto Rúa Muñoz (2026). *Laplacian Eigenvectors of Generically Weighted Graphs Have Pairwise Distinct Coordinates*. DOI: [10.48550/arXiv.2611.21979](https://doi.org/10.48550/arXiv.2611.21979). URL: <https://arxiv.org/abs/2611.21979v1>.

*Commentary.*

The loopless digraph contains a spanning out-arborescence. Path in T means a directed quiver path using the arcs of T, with the empty path allowed at the root. Rows receive arcs, so entry (i,j) of the adjacency reads the arc from j to i. The receiving-degree Laplacian is the diagonal row-sum matrix minus that adjacency, with entries then embedded in the complex numbers. The distinct-coordinate requirement applies at nonzero eigenvalues.

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

*Resolves.* `Problems/pineda-montoya-et-al-2026-separating-weights-question-7-5` (refuted) by `D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"pineda-montoya-et-al-2026-separating-weights-question-7-5","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/PinedaSeparatingWeightsRefutation.result","resolution_kind":"refuted"} -->

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
