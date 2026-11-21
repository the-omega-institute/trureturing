# Krebs–Leyva Conjecture 1.2

## Abstract

Rank-three standardized Abelian Cayley graphs can contain four-cliques at unbounded row counts.

**Definition 1.1 (The fixed-rank stabilization conjecture).**

$$claim \Leftrightarrow \left(\forall r \in \mathbb{N},\; 0 < r \Rightarrow \left(\exists m0 \in \mathbb{N},\; \forall m \in \mathbb{N},\; m0 \le m \Rightarrow \left(\forall M \in \mathbb{Z}^{m \times r},\; \left(\forall i \in \operatorname{Fin}\left(m\right),\; \exists j \in \operatorname{Fin}\left(r\right),\; M\left(i, j\right) \ne 0\right) \Rightarrow \left(\left(\neg \operatorname{IsBipartite}\left(M\right)\right) \Rightarrow \left(\left(\neg \operatorname{HasLoops}\left(M\right)\right) \Rightarrow \operatorname{chromaticNumber}\left(M\right) = 3\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.claim` (`✓ std3`).

*Citation.* Mike Krebs, Alejandro Leyva (2025). *Chromatic numbers of rank-two Abelian Cayley graphs*. DOI: [10.48550/arXiv.2511.03028](https://doi.org/10.48550/arXiv.2511.03028). URL: <https://arxiv.org/abs/2511.03028v1>.

*Commentary.*

Conjecture 1.2 is on printed page 3 of arXiv:2511.03028v1. The rank is the number of columns. The threshold m₀ can depend on the positive rank r. At every row count m at or above that threshold, the implication ranges over all integer matrices of size m by r.

The vertices of the source graph are the cosets of the integer span of the matrix columns. Its generator set consists of the two signs of each standard coordinate coset. Zero in that set is exactly the loop condition. Bipartiteness means looplessness and two-colorability of the simple Cayley graph. The source chromatic number has value infinity when a loop occurs and otherwise is the Mathlib chromatic number.

**Theorem 1.2 (A rank-three family with four-cliques).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.result` (`✓ std3`). ∎

*Resolves.* `Problems/krebs-leyva-2025-conjecture-1-2` (refuted) by `D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"krebs-leyva-2025-conjecture-1-2","declaration_gid":"D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mike Krebs, Alejandro Leyva (2025). *Chromatic numbers of rank-two Abelian Cayley graphs*. DOI: [10.48550/arXiv.2511.03028](https://doi.org/10.48550/arXiv.2511.03028). URL: <https://arxiv.org/abs/2511.03028v1>.

*Commentary.*

At row count 4(k + 1) + 3 the three columns are e₂ − 2e₁, e₃ − 3e₁, and 4e₁ + Σⱼ j fⱼ, where fⱼ denotes the jth additional coordinate and 1 ≤ j ≤ 4(k + 1). Each row is nonzero. If a coordinate vector were a column combination, its first five row equations would force all three coefficients to be zero, which contradicts its unit entry. Thus both signs of every coordinate coset are nonzero.

In the quotient the first two columns give [e₂] = 2[e₁] and [e₃] = 3[e₁]. The four vertices 0, [e₁], 2[e₁], 3[e₁] are pairwise adjacent because each positive-index difference is a nonzero coordinate generator. The graph therefore fails two-colorability and has chromatic number at least four. Taking k = m₀ supplies a witness past every proposed threshold at rank three.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/Coloring/KrebsC12Settlement.result`
