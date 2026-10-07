# An integer elliptic Sombor energy

## Abstract

Two four-cycles sharing a vertex have elliptic Sombor energy 144.

**Definition 1.1 (The elliptic Sombor matrix).**

$$\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (i : \operatorname{Fin}\left(n\right)), \forall (j : \operatorname{Fin}\left(n\right)), \operatorname{ellipticSomborMatrix}\left(G, i, j\right) = \left\{\begin{aligned}((\operatorname{val}\left(\operatorname{degree}\left(G, i\right)\right) : \mathbb{R}) + (\operatorname{val}\left(\operatorname{degree}\left(G, j\right)\right) : \mathbb{R})) \cdot \sqrt{(\operatorname{val}\left(\operatorname{degree}\left(G, i\right)\right) : \mathbb{R})^{2} + (\operatorname{val}\left(\operatorname{degree}\left(G, j\right)\right) : \mathbb{R})^{2}} & \text{if} \operatorname{Adj}\left(G, i, j\right)\\0 & \text{otherwise}\end{aligned}\right.$$

*Formalization.* `D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.ellipticSomborMatrix` (`✓ std3`).

*Citation.* Saeid Alikhani, Nima Ghanbari, Mohammad Ali Dehghanizadeh (2024). *Elliptic Sombor energy of a graph*. DOI: [10.48550/arXiv.2404.18622](https://doi.org/10.48550/arXiv.2404.18622). URL: <https://arxiv.org/abs/2404.18622v1>.

*Commentary.*

Abstract, page 1: "Let G be a simple graph with vertex set V(G) = {v₁, v₂, …, vₙ}. The elliptic Sombor matrix of G, denoted by A_ESO(G), is defined as the n×n matrix whose (i,j)-entry is (dᵢ+dⱼ)√(dᵢ²+dⱼ²) if vᵢ and vⱼ are adjacent and 0 for another cases." Vertices are labelled by Fin n, starting at zero. SimpleGraph.degree counts adjacent vertices. Typed val denotes the natural-number degree cast into ℝ before addition and squaring. Each entry is zero on a nonadjacent pair, including the diagonal.

**Definition 1.2 (Conjecture 3.9).**

$$claim \Leftrightarrow (\forall (n : \mathbb{N}), \forall (G : \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (hA : \operatorname{IsHermitian}\left(\operatorname{ellipticSomborMatrix}\left(G\right)\right)), \forall (z : \mathbb{Z}), \sum_{i : \operatorname{Fin}\left(n\right)} \lvert \operatorname{eigenvalues}\left(hA, i\right) \rvert \ne (\operatorname{val}\left(z\right) : \mathbb{R}))$$

*Formalization.* `D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.claim` (`✓ std3`).

*Citation.* Saeid Alikhani, Nima Ghanbari, Mohammad Ali Dehghanizadeh (2024). *Elliptic Sombor energy of a graph*. DOI: [10.48550/arXiv.2404.18622](https://doi.org/10.48550/arXiv.2404.18622). URL: <https://arxiv.org/abs/2404.18622v1>.

*Commentary.*

Conjecture 3.9, page 12: "There is no graph with integer-valued elliptic Sombor energy." Abstract, page 1: "The elliptic Sombor energy E_ESO of G is the sum of absolute values of the eigenvalues of A_ESO(G)." Encoding: n is a natural number, G is any simple graph on Fin n, and adjacency is decidable. The matrix is always Hermitian because adjacency is symmetric. hA is a proof of that property and supplies Mathlib's eigenvalues, indexed by Fin n with algebraic multiplicity. The sum is independent of the choice of Hermitian proof. Every integer z is cast to ℝ; the claim excludes equality to all such casts. The empty graph is included in this literal all-graphs statement; the counterexample below has seven vertices and no isolated vertex.

**Theorem 1.3 (Two squares with a common vertex).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/alikhani-ghanbari-dehghanizadeh-2024-elliptic-sombor-energy-integer-refutation` (refuted) by `D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"alikhani-ghanbari-dehghanizadeh-2024-elliptic-sombor-energy-integer-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Saeid Alikhani, Nima Ghanbari, Mohammad Ali Dehghanizadeh (2024). *Elliptic Sombor energy of a graph*. DOI: [10.48550/arXiv.2404.18622](https://doi.org/10.48550/arXiv.2404.18622). URL: <https://arxiv.org/abs/2404.18622v1>.

*Commentary.*

Use the edges 0–1–2–3–0 and 0–4–5–6–0. Vertex zero has degree four and every other vertex has degree two. The four edges incident to zero have weight 12√5, and the other four have weight 8√2. An explicit invertible change of basis diagonalizes this real symmetric matrix with diagonal entries −56, −16, 0, 0, 0, 16, 56. Its characteristic polynomial is x³(x−56)(x+56)(x−16)(x+16). Mathlib's spectral theorem identifies the roots with the Hermitian eigenvalue multiset. The absolute values therefore sum to 144, an integer, so the conjecture is false.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.ellipticSomborMatrix`
- Truth anchor: `D5/S3/Combinatorics/Graph/EllipticSomborEnergyIntegerRefutation.result`
