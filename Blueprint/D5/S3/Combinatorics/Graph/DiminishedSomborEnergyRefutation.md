# Zero energy of the edgeless graph

## Abstract

The edgeless graph has zero diminished Sombor matrix, zero eigenvalues and zero energy. Since zero is an integer, it refutes Movahedi's Conjecture 5.1.

**Definition 1.1 (The diminished Sombor matrix).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (i : \operatorname{Fin}\left(n\right)), \forall (j : \operatorname{Fin}\left(n\right)), \operatorname{diminishedSomborMatrix}\left(G\right)\left(i, j\right) = \operatorname{ite}\left(\operatorname{Adj}\left(G, i, j\right), \frac{\operatorname{Real.sqrt}\left((\operatorname{SimpleGraph.degree}\left(G, i\right) : \mathbb{R})^{2} + (\operatorname{SimpleGraph.degree}\left(G, j\right) : \mathbb{R})^{2}\right)}{(\operatorname{SimpleGraph.degree}\left(G, i\right) : \mathbb{R}) + (\operatorname{SimpleGraph.degree}\left(G, j\right) : \mathbb{R})}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.diminishedSomborMatrix` (`✓ std3`).

*Citation.* F. Movahedi (2025). *Diminished Sombor matrix, spectral radius, and energy of the graphs*. DOI: [10.48550/arXiv.2508.06531](https://doi.org/10.48550/arXiv.2508.06531). URL: <https://arxiv.org/abs/2508.06531v1>.

*Commentary.*

Page 2: "Motivated by this newly introduced index, and following on the approach in [5, 28], we introduce the diminished Sombor matrix for the graph G, denoted by ℳ = M_DS(G) = (μ_ij), of order n as follows". The displayed entry is sqrt(d_i² + d_j²)/(d_i + d_j) on edges and zero otherwise. SimpleGraph.degree supplies the vertex degrees, explicitly cast from natural numbers to real numbers before squaring, addition and division. ite is Lean's if-then-else. Vertices are Fin n, labelled 0 through n−1; relabelling the source's 1 through n does not change the spectrum. On an edge both degrees are positive, so its denominator is positive. On a non-edge the zero branch applies, with no quotient evaluated.

**Definition 1.2 (The diminished Sombor energy).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (h : \operatorname{Matrix.IsHermitian}\left(\operatorname{diminishedSomborMatrix}\left(G\right)\right)), \operatorname{diminishedSomborEnergy}\left(G\right) = \sum_{i : \operatorname{Fin}\left(n\right)} \left|\operatorname{Matrix.IsHermitian.eigenvalues}\left(h, i\right)\right|$$

*Formalization.* `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.diminishedSomborEnergy` (`✓ std3`).

*Citation.* F. Movahedi (2025). *Diminished Sombor matrix, spectral radius, and energy of the graphs*. DOI: [10.48550/arXiv.2508.06531](https://doi.org/10.48550/arXiv.2508.06531). URL: <https://arxiv.org/abs/2508.06531v1>.

*Commentary.*

Page 2: "We define the diminished Sombor energy as follows", followed by E_DSO(G) = ∑_{i=1}^n |λ_i|. The source's eigenvalues are real and counted with multiplicity. The real matrix is symmetric because adjacency is symmetric and both degree sums are symmetric. The definition proves this Hermitian property locally and uses Mathlib's Matrix.IsHermitian.eigenvalues, indexed by Fin n. In the formula h is any proof of that same Hermitian property; proof irrelevance makes its choice immaterial. This proof binder exposes the local proof argument of the spectral function, not an additional graph hypothesis. The sum is over all n eigenvalues, with multiplicity, and its order does not affect the energy.

**Definition 1.3 (Conjecture 5.1).**

$$claim \Leftrightarrow (\forall (n : \mathbb{N}), (1 \le n) \Rightarrow (\forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \neg (\exists (z : \mathbb{Z}), \operatorname{diminishedSomborEnergy}\left(G\right) = (z : \mathbb{R}))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.claim` (`✓ std3`).

*Citation.* F. Movahedi (2025). *Diminished Sombor matrix, spectral radius, and energy of the graphs*. DOI: [10.48550/arXiv.2508.06531](https://doi.org/10.48550/arXiv.2508.06531). URL: <https://arxiv.org/abs/2508.06531v1>.

*Commentary.*

Section 5, page 19: "There does not exist a graph whose diminished Sombor energy is an integer value." The encoding quantifies over positive orders n and all simple graphs on Fin n with decidable adjacency. An integer value means equality in the reals with the cast of some z : ℤ. No edge or connectedness condition appears in the conjecture. The paper itself includes edgeless graphs in the equality case of its upper energy bound.

**Theorem 1.4 (An integer energy counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/movahedi-2025-diminished-sombor-energy-integer` (refuted) by `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"movahedi-2025-diminished-sombor-energy-integer","declaration_gid":"D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* F. Movahedi (2025). *Diminished Sombor matrix, spectral radius, and energy of the graphs*. DOI: [10.48550/arXiv.2508.06531](https://doi.org/10.48550/arXiv.2508.06531). URL: <https://arxiv.org/abs/2508.06531v1>.

*Commentary.*

Take the edgeless graph on Fin 1. Every matrix entry is zero by the non-edge branch. Mathlib's Hermitian spectral theorem identifies a zero matrix with an identically zero eigenvalue function, so the energy is zero. Choosing the integer zero contradicts the conjecture. This argument concerns the literal all-graphs statement; nonintegrality for graphs with at least one edge remains open.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.diminishedSomborEnergy`
- Truth anchor: `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.diminishedSomborMatrix`
- Truth anchor: `D5/S3/Combinatorics/Graph/DiminishedSomborEnergyRefutation.result`
