# The triangle refutes Li–Guo Conjecture 2.22

## Abstract

The triangle has signless Laplacian eigenvalues 4, 1, 1. Its truncated square sum is 4, exceeding the degree bound 3 in Li–Guo Conjecture 2.22.

**Definition 1.1 (The truncated spectral square sum).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{TQ}\left(G\right) = \operatorname{Multiset.sum}\left(\operatorname{Multiset.map}\left((fun (q : \mathbb{R}) \mapsto \operatorname{max}\left((q - 2), 0\right)^{2}), \operatorname{graphSpectrum}\left(G, \operatorname{MatrixKind.signless}\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.TQ` (`✓ std3`).

*Citation.* Wen-Jun Li; Ji-Ming Guo (2025). *A new conjecture on Laplacian eigenvalues and degree sequence of a graph*. DOI: [10.2298/FIL2513551L](https://doi.org/10.2298/FIL2513551L). URL: <https://www.pmf.ni.ac.rs/filomat-content/2025/39-13/39-13-22-25952.pdf>.

*Commentary.*

Li and Guo, p. 4551: "Let Q(G)=D(G)+A(G) be the signless Laplacian matrix of G and q₁(G)≥q₂(G)≥⋯≥qₙ(G) be the signless Laplacian eigenvalues of G." The graphSpectrum multiset of sourceMatrix G MatrixKind.signless contains every real eigenvalue with its multiplicity. The source sum on p. 4564 is over indices with qᵢ ≥ 2. Replacing its summand by max(q−2,0)² on all indices preserves the value, including q = 2. SimpleGraph (Fin n) describes a finite simple undirected loopless graph.

**Definition 1.2 (The degree bound).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), \operatorname{R}\left(G\right) = (1 - \frac{1}{(\operatorname{SimpleGraph.maxDegree}\left(G\right) : \mathbb{R})}) \cdot (\sum_{i : \operatorname{Fin}\left(n\right)} (\operatorname{SimpleGraph.degree}\left(G, i\right) : \mathbb{R}) \cdot ((\operatorname{SimpleGraph.degree}\left(G, i\right) : \mathbb{R}) - 1))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.R` (`✓ std3`).

*Citation.* Wen-Jun Li; Ji-Ming Guo (2025). *A new conjecture on Laplacian eigenvalues and degree sequence of a graph*. DOI: [10.2298/FIL2513551L](https://doi.org/10.2298/FIL2513551L). URL: <https://www.pmf.ni.ac.rs/filomat-content/2025/39-13/39-13-22-25952.pdf>.

*Commentary.*

Li and Guo, p. 4551: "Let G be a graph with n vertices and m edges, and d₁(G)≥d₂(G)≥⋯≥dₙ(G) be the degree sequence of G." The factor d₁ in Conjecture 2.22 is SimpleGraph.maxDegree. The sum over vertices equals the sum over the decreasing degree sequence, since every vertex occurs once. Every degree is cast to ℝ before subtraction or division; subtraction is real subtraction.

**Definition 1.3 (Conjecture 2.22).**

$$\operatorname{claim} \Leftrightarrow (\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (0 < \operatorname{SimpleGraph.maxDegree}\left(G\right)) \Rightarrow \operatorname{TQ}\left(G\right) \le \operatorname{R}\left(G\right))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.claim` (`✓ std3`).

*Citation.* Wen-Jun Li; Ji-Ming Guo (2025). *A new conjecture on Laplacian eigenvalues and degree sequence of a graph*. DOI: [10.2298/FIL2513551L](https://doi.org/10.2298/FIL2513551L). URL: <https://www.pmf.ni.ac.rs/filomat-content/2025/39-13/39-13-22-25952.pdf>.

*Commentary.*

Li and Guo, Conjecture 2.22, p. 4564: "Let G be a graph with degree sequence d₁≥d₂≥⋯≥dₙ. Then" followed by ∑_{qᵢ≥2}(qᵢ−2)²≤(1−1/d₁)∑_{i=1}ⁿdᵢ(dᵢ−1). Here n ranges over ℕ and G over SimpleGraph (Fin n). The denominator 1/d₁ restricts the assertion to positive maximum degree. There is no connectedness or regularity restriction. TQ and R are the two displayed sides, and the spectral multiset counts repeated eigenvalues separately.

**Theorem 1.4 (A triangle counterexample).**

$$\neg (\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), (0 < \operatorname{SimpleGraph.maxDegree}\left(G\right)) \Rightarrow \operatorname{TQ}\left(G\right) \le \operatorname{R}\left(G\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/li-guo-signless-laplacian` (refuted) by `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"li-guo-signless-laplacian","declaration_gid":"D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Wen-Jun Li; Ji-Ming Guo (2025). *A new conjecture on Laplacian eigenvalues and degree sequence of a graph*. DOI: [10.2298/FIL2513551L](https://doi.org/10.2298/FIL2513551L). URL: <https://www.pmf.ni.ac.rs/filomat-content/2025/39-13/39-13-22-25952.pdf>.

*Commentary.*

For SimpleGraph.cycleGraph 3 every degree and the maximum degree equal 2. The signless Laplacian is the real matrix [[2,1,1],[1,2,1],[1,1,2]], with characteristic polynomial (X−4)(X−1)(X−1). The Hermitian characteristic-root theorem gives the eigenvalue multiset {4,1,1}, retaining both copies of 1. Hence TQ = 4 and R = 3. Applying the asserted inequality to this positive-degree graph would give 4 ≤ 3. This proves the negation for the whole stated class; an infinite cycle-family formula is not asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.R`
- Truth anchor: `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.TQ`
- Truth anchor: `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SignlessLaplacian/LiGuoDegreeSequenceRefutation.result`
- Dependency: [D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation](../SubgroupGenerating/CyclicExtensionRefutation.md)
