# An integer Sombor energy

## Abstract

The graph formed by three four-cycles sharing one vertex has Sombor spectrum 16, -16, 4, -4, 4, -4, 0, 0, 0, 0. Its Sombor energy is 48, refuting Conjecture 3.8 of Ghanbari.

**Definition 1.1 (The Sombor matrix).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (i : \operatorname{Fin}\left(n\right)), \forall (j : \operatorname{Fin}\left(n\right)), \operatorname{somborMatrix}\left(G, i, j\right) = \left\{\begin{aligned}\operatorname{Real.sqrt}\left((\operatorname{degree}\left(G, i\right) : \mathbb{R})^{2} + (\operatorname{degree}\left(G, j\right) : \mathbb{R})^{2}\right) & \text{if} \operatorname{Adj}\left(G, i, j\right)\\0 & \text{otherwise}\end{aligned}\right.$$

*Formalization.* `D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.somborMatrix` (`✓ std3`).

*Citation.* Nima Ghanbari (2022). *On the Sombor characteristic polynomial and Sombor energy of a graph*. DOI: [10.1007/s40314-022-01957-5](https://doi.org/10.1007/s40314-022-01957-5). URL: <https://arxiv.org/abs/2108.08552v1>.

*Commentary.*

Abstract, page 1: "Let G be a simple graph with vertex set V(G) = {v₁, v₂, …, vₙ}. The Sombor matrix of G, denoted by A_SO(G), is defined as the n×n matrix whose (i,j)-entry is √(dᵢ²+dⱼ²) if vᵢ and vⱼ are adjacent and 0 for another cases." Here G is Mathlib's SimpleGraph on Fin n, labelled 0 through n−1, Adj is its adjacency relation, and degree is SimpleGraph.degree, the number of adjacent vertices. The degrees are cast to real numbers before squaring. The formula gives each entry of somborMatrix G; its type is Matrix (Fin n) (Fin n) ℝ.

**Definition 1.2 (Conjecture 3.8).**

$$claim \Leftrightarrow (\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \text{let} hA : \operatorname{Matrix.IsHermitian}\left(\operatorname{somborMatrix}\left(G\right)\right), \forall (z : \mathbb{Z}), \sum_{i : \operatorname{Fin}\left(n\right)} \left|\operatorname{Matrix.IsHermitian.eigenvalues}\left(hA, i\right)\right| \ne (z : \mathbb{R}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.claim` (`✓ std3`).

*Citation.* Nima Ghanbari (2022). *On the Sombor characteristic polynomial and Sombor energy of a graph*. DOI: [10.1007/s40314-022-01957-5](https://doi.org/10.1007/s40314-022-01957-5). URL: <https://arxiv.org/abs/2108.08552v1>.

*Commentary.*

Conjecture 3.8, page 13: "There is no graph with integer-valued Sombor energy." The Abstract, page 1, states: "The Sombor energy En_SO of G is the sum of absolute values of the eigenvalues of A_SO(G)." Section 1 specifies finite simple graphs without directed, multiple or weighted edges or self-loops. Every finite labelled graph is represented by SimpleGraph (Fin n). The Hermitian proof hA is constructed from symmetry of adjacency and of the sum of squared degrees; let hA in the formula denotes this proof, with its proof term implicit. Matrix.IsHermitian.eigenvalues lists the real eigenvalues with multiplicity. The sum ranges over all i : Fin n and is written inline. Comparing it to every integer z cast to ℝ expresses precisely nonintegrality. DecidableRel is an anonymous instance argument, not an extra restriction on a finite graph.

**Theorem 1.3 (Three four-cycles sharing a vertex).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/ghanbari-2022-sombor-energy-integer-refutation` (refuted) by `D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ghanbari-2022-sombor-energy-integer-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nima Ghanbari (2022). *On the Sombor characteristic polynomial and Sombor energy of a graph*. DOI: [10.1007/s40314-022-01957-5](https://doi.org/10.1007/s40314-022-01957-5). URL: <https://arxiv.org/abs/2108.08552v1>.

*Commentary.*

Take the cycles 0–1–2–3–0, 0–4–5–6–0 and 0–7–8–9–0. Vertex 0 has degree six; all other vertices have degree two. Thus the six central edges have weight a = √40 and the remaining six edges have weight b = √8. An explicit ten-column eigenvector matrix P has eigenvalues d = (16, -16, 4, -4, 4, -4, 0, 0, 0, 0) and satisfies PᵀP = diagonal(768, 768, 32, 32, 96, 96, 2, 2, 2, 128). Consequently Q = diagonal(768⁻¹, 768⁻¹, 32⁻¹, 32⁻¹, 96⁻¹, 96⁻¹, 2⁻¹, 2⁻¹, 2⁻¹, 128⁻¹)Pᵀ is its inverse. The identity somborMatrix G · P = P · diagonal d gives characteristic polynomial x⁴(x−16)(x+16)(x−4)²(x+4)². The Hermitian spectral theorem identifies its root multiset with the eigenvalue multiset. The absolute values sum to 48, contradicting claim at z = 48.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/SomborEnergyIntegerRefutation.somborMatrix`
