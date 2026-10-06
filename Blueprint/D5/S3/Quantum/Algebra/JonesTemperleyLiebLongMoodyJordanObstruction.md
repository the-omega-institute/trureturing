# The Jordan obstruction for the Jones-Temperley-Lieb endpoint-sector seeds

## Abstract

Negami (arXiv:2610.00293, Problem 6.8) asks for a proof of the Jordan obstruction observed numerically for Katz-Long-Moody seeds built from the endpoint sectors of the Jones-Temperley-Lieb path representations. For every n >= 3, every level ell >= 4 and every endpoint sector of dimension at least two, every seed generator g_j has no fixed vector, so K = 0, and the ambient Long-Moody operator S_1 has a Jordan chain of length two at the eigenvalue -alpha^(-3).

**Definition 1.1 (The A graph).**

$$\forall \ell : \mathbb{N}, \forall a : \operatorname{Fin}\left(\ell - 1\right), \forall b : \operatorname{Fin}\left(\ell - 1\right), \operatorname{adj}\left(\ell, a, b\right) \Leftrightarrow ((\operatorname{val}\left(a\right) + 1 = \operatorname{val}\left(b\right)) \lor (\operatorname{val}\left(b\right) + 1 = \operatorname{val}\left(a\right)))$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.adj` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

Vertices are the elements of Fin(ell - 1); vertex a is the paper's vertex a + 1 of the A_(ell-1) graph, and two vertices are adjacent when their labels differ by one.

**Definition 1.2 (The Perron-Frobenius weights).**

$$\forall \ell : \mathbb{N}, \forall a : \operatorname{Fin}\left(\ell - 1\right), \operatorname{mu}\left(\ell, a\right) = \operatorname{sin}\left(\frac{(\operatorname{val}\left(a\right) + 1) \cdot \pi}{\ell}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.mu` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

mu(a) = sin((a + 1) pi/ell), the standard path-model weight of vertex a + 1.

**Definition 1.3 (The loop value).**

$$\forall \ell : \mathbb{N}, \operatorname{delta}\left(\ell\right) = 2 \cdot \operatorname{cos}\left(\frac{\pi}{\ell}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.delta` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

delta_ell = 2 cos(pi/ell), the value with E_i^2 = delta_ell E_i.

**Definition 1.4 (The left endpoint).**

$$\forall \ell : \mathbb{N}, \forall h : (2 \le \ell), \operatorname{val}\left(\operatorname{v1}\left(\ell, h\right)\right) = 0$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.v1` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

The first vertex, the paper's vertex 1, at which every path starts.

**Definition 1.5 (The endpoint sectors).**

$$\forall \ell : \mathbb{N}, \forall n : \mathbb{N}, \forall h : (2 \le \ell), \forall t : \operatorname{Fin}\left(\ell - 1\right), \operatorname{Sector}\left(\ell, n, h, t\right) = \operatorname{LegalPath}\left(\operatorname{adj}\left(\ell\right), n + 1, \operatorname{v1}\left(\ell, h\right), t\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.Sector` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

Sector(ell, n, t) is the basis of the endpoint sector of the length-(n + 1) paths on the A graph that start at the left endpoint and end at t, the frozen LegalPath type.

**Definition 1.6 (The path-model Temperley-Lieb operators).**

$$\forall \ell : \mathbb{N}, \forall n : \mathbb{N}, \forall h : (2 \le \ell), \forall t : \operatorname{Fin}\left(\ell - 1\right), \forall j : \mathbb{N}, \operatorname{E}\left(\ell, n, h, t, j\right) = \operatorname{ite}\left(j < n, \operatorname{delta}\left(\ell\right) \cdot \operatorname{pathProjection}\left(\operatorname{adj}\left(\ell\right), \operatorname{mu}\left(\ell\right), \operatorname{delta}\left(\ell\right), n + 1, \operatorname{v1}\left(\ell, h\right), t, j + 1\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.E` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

E_j, for j < n, is delta times the frozen weighted path projection at interior vertex j + 1: it vanishes unless the vertices j and j + 2 of the path agree at some c, and then replaces vertex j + 1 by each neighbour d of c with coefficient sqrt(mu(h) mu(d))/mu(c). For j >= n it is 0.

**Definition 1.7 (The braid phase).**

$$\forall \ell : \mathbb{N}, \operatorname{alpha}\left(\ell\right) = i \cdot \operatorname{exp}\left(\frac{-\pi i}{2 \cdot \ell}\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.alpha` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

alpha_ell = i exp(-pi i/(2 ell)), with beta_ell = alpha_ell^(-1) and no additional scalar twist.

**Definition 1.8 (The braid generators).**

$$\forall \ell : \mathbb{N}, \forall n : \mathbb{N}, \forall h : (2 \le \ell), \forall t : \operatorname{Fin}\left(\ell - 1\right), \forall j : \mathbb{N}, \operatorname{rho}\left(\ell, n, h, t, j\right) = \operatorname{alpha}\left(\ell\right) \cdot 1 + \operatorname{alpha}\left(\ell\right)^{-1} \cdot \operatorname{E}\left(\ell, n, h, t, j\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.rho` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

rho(sigma_j) = alpha I + alpha^(-1) E_j on an endpoint sector.

**Definition 1.9 (The seed braid generators).**

$$\forall \ell : \mathbb{N}, \forall n : \mathbb{N}, \forall h : (2 \le \ell), \forall t : \operatorname{Fin}\left(\ell - 1\right), \forall i : \mathbb{N}, \operatorname{s}\left(\ell, n, h, t, i\right) = \operatorname{rho}\left(\ell, n, h, t, i\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.s` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

s_i = rho(sigma_i), the action of the braid generators of B_n inside B_(n+1).

**Definition 1.10 (The seed free generators).**

$$\forall \ell : \mathbb{N}, \forall n : \mathbb{N}, \forall h : (2 \le \ell), \forall t : \operatorname{Fin}\left(\ell - 1\right), (\operatorname{seed}\left(\ell, n, h, t, 0\right) = \operatorname{rho}\left(\ell, n, h, t, 0\right) \cdot \operatorname{rho}\left(\ell, n, h, t, 0\right)) \land (\forall j : \mathbb{N}, \operatorname{seed}\left(\ell, n, h, t, j + 1\right) = \operatorname{s}\left(\ell, n, h, t, j + 1\right) \cdot \operatorname{seed}\left(\ell, n, h, t, j\right) \cdot \operatorname{s}\left(\ell, n, h, t, j + 1\right)^{-1})$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.seed` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

The images of x_1 = sigma_0^2 and x_(j+1) = sigma_j x_j sigma_j^(-1), zero-based: seed(0) = rho(0)^2 and seed(j + 1) = s(j + 1) seed(j) s(j + 1)^(-1).

**Definition 1.11 (The free-group images).**

$$\forall \ell : \mathbb{N}, \forall n : \mathbb{N}, \forall h : (2 \le \ell), \forall t : \operatorname{Fin}\left(\ell - 1\right), \forall j : \operatorname{Fin}\left(n\right), \operatorname{g}\left(\ell, n, h, t, j\right) = \operatorname{seed}\left(\ell, n, h, t, \operatorname{val}\left(j\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.g` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

g(j) for j in Fin(n) is seed(j), the paper's g_(j+1) = rho(x_(j+1)).

**Definition 1.12 (The ambient Long-Moody operator).**

$$\forall \ell : \mathbb{N}, \forall n : \mathbb{N}, \forall h : (2 \le \ell), \forall t : \operatorname{Fin}\left(\ell - 1\right), \forall k : \operatorname{Fin}\left(n\right), \forall l : \operatorname{Fin}\left(n\right), \forall x : \operatorname{Sector}\left(\ell, n, h, t\right), \forall y : \operatorname{Sector}\left(\ell, n, h, t\right), \operatorname{S1}\left(\ell, n, h, t\right)\left((k, x), (l, y)\right) = \operatorname{ite}\left((\operatorname{val}\left(k\right) = 0) \land (\operatorname{val}\left(l\right) = 1), (\operatorname{s}\left(\ell, n, h, t, 1\right) \cdot \operatorname{seed}\left(\ell, n, h, t, 0\right))\left(x, y\right), \operatorname{ite}\left((\operatorname{val}\left(k\right) = 1) \land (\operatorname{val}\left(l\right) = 0), (\operatorname{s}\left(\ell, n, h, t, 1\right))\left(x, y\right), \operatorname{ite}\left((\operatorname{val}\left(k\right) = 1) \land (\operatorname{val}\left(l\right) = 1), (\operatorname{s}\left(\ell, n, h, t, 1\right) \cdot (1 - \operatorname{seed}\left(\ell, n, h, t, 1\right)))\left(x, y\right), \operatorname{ite}\left((2 \le \operatorname{val}\left(k\right)) \land (k = l), (\operatorname{s}\left(\ell, n, h, t, 1\right))\left(x, y\right), 0\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.S1` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

Eq. (braid-matrices) at i = 1 on n slots, zero-based: on slots 0 and 1 the block s_1 (0, g_1; I, I - g_2), and s_1 on every other slot. In the formula S1 is written with entries indexed by (slot, path).

**Definition 1.13 (The eigenvalue).**

$$\forall \ell : \mathbb{N}, \operatorname{b}\left(\ell\right) = -(\operatorname{alpha}\left(\ell\right)^{-1})^{3}$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.b` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

b(ell) = -alpha_ell^(-3), the eigenvalue of rho(sigma_j) on the image of E_j.

**Definition 1.14 (The Jordan obstruction).**

$$claim \Leftrightarrow (\forall \ell : \mathbb{N}, \forall n : \mathbb{N}, \forall t : \operatorname{Fin}\left(\ell - 1\right), \forall hl : (4 \le \ell), (3 \le n) \Rightarrow (\operatorname{let} h : (2 \le \ell) := \operatorname{trans}\left(\operatorname{decide}, hl\right); ((2 \le \operatorname{card}\left(\operatorname{Sector}\left(\ell, n, h, t\right)\right)) \Rightarrow ((\forall j : \operatorname{Fin}\left(n\right), \forall v : \operatorname{Sector}\left(\ell, n, h, t\right) \to \mathbb{C}, (\operatorname{mulVec}\left(\operatorname{g}\left(\ell, n, h, t, j\right), v\right) = v) \Rightarrow (v = 0)) \land (\exists w : (\operatorname{Fin}\left(n\right) \times \operatorname{Sector}\left(\ell, n, h, t\right)) \to \mathbb{C}, (\operatorname{mulVec}\left(\operatorname{S1}\left(\ell, n, h, t\right) - \operatorname{b}\left(\ell\right) \cdot 1, \operatorname{mulVec}\left(\operatorname{S1}\left(\ell, n, h, t\right) - \operatorname{b}\left(\ell\right) \cdot 1, w\right)\right) = 0) \land (\operatorname{mulVec}\left(\operatorname{S1}\left(\ell, n, h, t\right) - \operatorname{b}\left(\ell\right) \cdot 1, w\right) \ne 0))))))$$

*Formalization.* `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.claim` (`✓ std3`).

*Citation.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

For every ell >= 4, n >= 3 and end vertex t whose sector has at least two paths (as in the Lean statement, h is let-bound to the proof of 2 <= ell obtained from hl : 4 <= ell, and the sector and the operators take it as an argument): no seed generator g_j has a nonzero fixed vector (so K = 0, the sectors admitted by the remark's test), and S_1 is not semisimple at b: some w has (S_1 - b)^2 w = 0 and (S_1 - b) w != 0.

**Theorem 1.15 (The Jordan obstruction holds for every endpoint sector).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.result` (`✓ std3`). ∎

*Resolves.* `Problems/negami-2026-jones-temperley-lieb-jordan-obstruction` (proved) by `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"negami-2026-jones-temperley-lieb-jordan-obstruction","declaration_gid":"D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* H. Negami (2026). *Quantum gates from the middle convolution of twisted Burau representations*. DOI: [10.48550/arXiv.2610.00293](https://doi.org/10.48550/arXiv.2610.00293). URL: <https://arxiv.org/abs/2610.00293v1>.

*Commentary.*

Put a = alpha_ell, delta = 2 cos(pi/ell) = -(a^2 + a^(-2)). The weights satisfy sum over neighbours of mu = delta mu (the boundary terms sin 0 and sin pi vanish), so the frozen Temperley-Lieb theorem gives E_j^2 = delta E_j and (rho_j - a)(rho_j + a^(-3)) = 0. Hence every g_j satisfies (g - a^2)(g - a^(-6)) = 0, and since ell >= 4 neither a^2 nor a^(-6) is 1, so g_j has no fixed vector. A sector with two paths contains a path beginning 1, 2, 1 and the same path with its vertex 2 replaced by 3 (vertex 3 exists as ell >= 4); on their span rho_0 and rho_1 act, in a suitable basis f_0, f_1, by (-a^(-3), a; 0, a) and (a, 0; a^(-3), -a^(-3)). On the four-dimensional subspace of slots 0 and 1 the operator S_1 is (0, UG; U, U(I - H)) with U = rho_1, G = rho_0^2, H = U G U^(-1), and an explicit Laurent-polynomial vector w gives (S_1 - b)^2 w = 0 and (S_1 - b) w = (a^6 - 1) times a nonzero vector, which is nonzero as a^6 != 1.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.E`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.S1`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.Sector`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.adj`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.alpha`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.b`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.claim`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.delta`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.g`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.mu`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.result`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.rho`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.s`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.seed`
- Truth anchor: `D5/S3/Quantum/Algebra/JonesTemperleyLiebLongMoodyJordanObstruction.v1`
- Dependency: [D5/S3/Quantum/Algebra/WeightedLegalPathTemperleyLieb](WeightedLegalPathTemperleyLieb.md)
