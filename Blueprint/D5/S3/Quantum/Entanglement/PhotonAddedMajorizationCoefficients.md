# Non-negativity of the photon-addition coefficients

## Abstract

For every k at least 2, the coefficients c_n^(kk) that compare k-photon addition with single-photon addition on a two-mode squeezed vacuum are non-negative. This proves the conjecture of Z. Van Herstraeten, N. J. Cerf, S. Guha and C. N. Gagatsos (arXiv:2312.02066), who proved the cases k = 2, ..., 8.

**Definition 1.1 (The expansion defining the coefficients).**

$$\operatorname{Expansion}\left(k, c\right) \Leftrightarrow (\forall n \in \mathbb{N}, \operatorname{C}\left(n + k + 1, k\right)^{2} = \sum_{i=0}^{n} c\left(n - i\right) \cdot (i + 1)^{2} + (n + 2)^{2})$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.Expansion` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Nicolas J. Cerf; Saikat Guha; Christos N. Gagatsos (2024). *Majorization theoretical approach to entanglement enhancement via local filtration*. DOI: [10.1103/PhysRevA.110.042430](https://doi.org/10.1103/PhysRevA.110.042430). URL: <https://arxiv.org/abs/2312.02066v2>.

*Commentary.*

For natural numbers k and a sequence c of real numbers indexed by n >= 0, Expansion(k, c) is the expansion of the paper, C(n+k+1, k)^2 = sum over i from 0 to n+1 of c_(n-i)^(kk) (i+1)^2 for every n >= 0, with c_n^(kk) = c(n) for n >= 0 and c_(-1)^(kk) = 1, so that the term i = n+1 is (n+2)^2. Here C(a, b) is the binomial coefficient.

**Definition 1.2 (The photon-addition conjecture).**

$$claim \Leftrightarrow (\forall k \in \mathbb{N}, (k \ge 2) \Rightarrow \left((\exists c \in \mathbb{R}^{\mathbb{N}}, \operatorname{Expansion}\left(k, c\right)) \land (\forall c \in \mathbb{R}^{\mathbb{N}}, (\operatorname{Expansion}\left(k, c\right)) \Rightarrow \forall n \in \mathbb{N}, 0 \le c\left(n\right))\right))$$

*Formalization.* `D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.claim` (`✓ std3`).

*Citation.* Zacharie Van Herstraeten; Nicolas J. Cerf; Saikat Guha; Christos N. Gagatsos (2024). *Majorization theoretical approach to entanglement enhancement via local filtration*. DOI: [10.1103/PhysRevA.110.042430](https://doi.org/10.1103/PhysRevA.110.042430). URL: <https://arxiv.org/abs/2312.02066v2>.

*Commentary.*

For every natural number k >= 2, a sequence c with Expansion(k, c) exists, and every such sequence takes only non-negative values. The expansion determines c(n) from c(0), ..., c(n-1), so these are the coefficients c_n^(kk) of the paper, and their non-negativity is the column stochasticity of the paper's matrix D.

**Theorem 1.3 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.result` (`✓ std3`). ∎

*Resolves.* `Problems/van-herstraeten-2024-photon-addition-coefficients` (proved) by `D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"van-herstraeten-2024-photon-addition-coefficients","declaration_gid":"D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zacharie Van Herstraeten; Nicolas J. Cerf; Saikat Guha; Christos N. Gagatsos (2024). *Majorization theoretical approach to entanglement enhancement via local filtration*. DOI: [10.1103/PhysRevA.110.042430](https://doi.org/10.1103/PhysRevA.110.042430). URL: <https://arxiv.org/abs/2312.02066v2>.

*Commentary.*

Let N_k(x) be the power series with coefficients C(n+k, k)^2. The expansion says (1 + sum of c(n) x^(n+1)) N_1 = N_k. First, N_1 = (1+x)(1-x)^(-3), since C(n+2, 2) + C(n+1, 2) = (n+1)^2. Second, by Vandermonde's identity C(n+k, k) is the sum over j of C(k, j) C(n, j), and C(n+k, k) C(n, j) = C(k+j, j) C(n+k, k+j); so with a_j = C(k, j) C(k+j, j), N_k is the sum over j from 0 to k of a_j x^j (1-x)^(-(k+j+1)). Let E = (1-x^2)^(-1), the series 1 + x^2 + x^4 + ..., and let B = (1 + (k^2+k-1) x)(1-x)^(-(k-2)) E + sum over j from 2 to k of a_j x^j (1-x)^(-(k+j-3)) E. Since E(1+x) = (1-x)^(-1), (1 - x)(1-x)^(-(k+2)) = (1-x)^(-(k+1)), a_0 = 1 and a_1 = k(k+1), one gets B N_1 = N_k. For k >= 2 every factor of B has non-negative coefficients and B has constant term 1, so c(n) = [x^(n+1)] B is a solution. As N_1 is not a zero divisor, every solution equals it, and its values are non-negative.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.Expansion`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/PhotonAddedMajorizationCoefficients.result`
