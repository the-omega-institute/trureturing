# Gupta's rectangular-grid dispersion inequality

## Abstract

Integer grid Lipschitz functions satisfy Gupta's dispersion bound.

Sorting the rows and then the columns preserves the value multiset and adjacent differences bounded by one. The sorted function and its remainder from the coordinate sum are increasing. FKG compares their centered absolute deviations. An integer center is no worse than a rational center, and reflection minimizes the coordinate-sum cost at its mean.

**Definition 1.1 (Integer functions with adjacent differences at most one).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall phi \in \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{Z},\; \operatorname{IsLipschitz}\left(phi\right) = (\forall u \in \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right),\; \forall v \in \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right),\; ((\operatorname{SimpleGraph}.\operatorname{boxProd}\left(\operatorname{SimpleGraph}.\operatorname{pathGraph}\left(m\right), \operatorname{SimpleGraph}.\operatorname{pathGraph}\left(n\right)\right)).\operatorname{Adj}\left(u, v\right)) \Rightarrow \lvert phi\left(u\right) - phi\left(v\right) \rvert \le 1)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.IsLipschitz` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *Height functions on the m × n Miura-ori flip graph: degree sequence and diameter*. DOI: [10.48550/arXiv.2606.22614](https://doi.org/10.48550/arXiv.2606.22614). URL: <https://arxiv.org/abs/2606.22614v2>.

*Commentary.*

Section 2, p. 2: “Every construction in this paper lives on the grid graph Gm,n, with vertex set {(i, j) : 1 ≤ i ≤ m, 1 ≤ j ≤ n} and each vertex joined to its horizontal and vertical neighbours;” The source cell (i,j) corresponds to (i−1,j−1) in Fin m × Fin n. An integer function on the grid is 1-Lipschitz when the absolute difference on each edge is at most one. No origami realisability hypothesis is imposed.

**Definition 1.2 (Integer median-dispersion).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall phi \in \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{Z},\; \operatorname{disp}\left(phi\right) = \operatorname{sInf}\left(\operatorname{Set}.\operatorname{range}\left(\lambda (K:\mathbb{Z}) \mapsto \sum_{v:\operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right)} \operatorname{Int}.\operatorname{natAbs}\left(phi\left(v\right) - K\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.disp` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *Height functions on the m × n Miura-ori flip graph: degree sequence and diameter*. DOI: [10.48550/arXiv.2606.22614](https://doi.org/10.48550/arXiv.2606.22614). URL: <https://arxiv.org/abs/2606.22614v2>.

*Commentary.*

Section 4, p. 13: “Writing disp(ϕ) = min_{K∈Z} Σ_v |ϕ(v) − K| for the ℓ1 median-dispersion of an integer function ϕ on the grid”. The sum counts each vertex once. Int.natAbs is the natural absolute value, and sInf is taken in ℕ over a nonempty range of integer-center costs, hence gives their minimum.

**Definition 1.3 (Dispersion of the coordinate sum).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{D}\left(m, n\right) = \operatorname{sInf}\left(\operatorname{Set}.\operatorname{range}\left(\lambda (K:\mathbb{Z}) \mapsto \sum_{i:\operatorname{Fin}\left(m\right)} \sum_{j:\operatorname{Fin}\left(n\right)} \operatorname{Int}.\operatorname{natAbs}\left(((i:\mathbb{Z}) + 1) + ((j:\mathbb{Z}) + 1) - K\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.D` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *Height functions on the m × n Miura-ori flip graph: degree sequence and diameter*. DOI: [10.48550/arXiv.2606.22614](https://doi.org/10.48550/arXiv.2606.22614). URL: <https://arxiv.org/abs/2606.22614v2>.

*Commentary.*

Theorem 4.1, p. 13: “Let D(m, n) = min_{K∈Z} Σ_{i=1}^m Σ_{j=1}^n |(i + j) − K|. Then diam OFG(M_{m,n}) ≥ D(m, n) for all m, n ≥ 1.” The casts of i and j to ℤ are followed by addition of one, preserving the source's one-indexed coordinate sum. The infimum and summands are natural-valued.

**Definition 1.4 (Gupta inequality (4)).**

$$claim = (\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall phi \in \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{Z},\; (\operatorname{IsLipschitz}\left(phi\right)) \Rightarrow \operatorname{disp}\left(phi\right) \le \operatorname{D}\left(m, n\right))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.claim` (`✓ std3`).

*Citation.* Chakshu Gupta (2026). *Height functions on the m × n Miura-ori flip graph: degree sequence and diameter*. DOI: [10.48550/arXiv.2606.22614](https://doi.org/10.48550/arXiv.2606.22614). URL: <https://arxiv.org/abs/2606.22614v2>.

*Commentary.*

Inequality (4), p. 14: “By Proposition 4.2 and Theorem 4.1, the diameter equals D(m, n) as soon as no integer 1-Lipschitz function on G_{m,n}, realisable or not, has dispersion exceeding D(m, n): max_ϕ disp(ϕ) ≤ D(m, n). (4)” Here phi denotes the source's ϕ, the dimensions range over ℕ, and the statement also includes empty grids, whose dispersion is zero.

**Theorem 1.5 (The rectangular-grid dispersion bound).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall phi \in \operatorname{Fin}\left(m\right) \times \operatorname{Fin}\left(n\right) \to \mathbb{Z},\; (\operatorname{IsLipschitz}\left(phi\right)) \Rightarrow \operatorname{disp}\left(phi\right) \le \operatorname{D}\left(m, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.result` (`✓ std3`). ∎

*Resolves.* `Problems/gupta-2026-miura-grid-dispersion-inequality-4` (proved) by `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gupta-2026-miura-grid-dispersion-inequality-4","declaration_gid":"D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chakshu Gupta (2026). *Height functions on the m × n Miura-ori flip graph: degree sequence and diameter*. DOI: [10.48550/arXiv.2606.22614](https://doi.org/10.48550/arXiv.2606.22614). URL: <https://arxiv.org/abs/2606.22614v2>.

*Commentary.*

Every integer 1-Lipschitz function on every finite rectangular grid has median-dispersion at most D(m,n). Row and column sorting reduce the estimate to increasing functions, and the centered FKG comparison bounds their absolute deviations by those of the coordinate sum. Reflection pairs that sum around its mean. The source's Theorem 4.1 and Proposition 4.2 then give the stated origami diameter for positive rectangles; those origami reductions and the separate abstract ν-chain conjecture are outside this theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.D`
- Truth anchor: `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.IsLipschitz`
- Truth anchor: `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.claim`
- Truth anchor: `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.disp`
- Truth anchor: `D5/S3/Combinatorics/Geometry/GuptaMiuraGridDispersion.result`
- Dependency: [D5/S3/Combinatorics/Graph/Domination/LeeLiuThreeRowIntegerDomination](../Graph/Domination/LeeLiuThreeRowIntegerDomination.md)
