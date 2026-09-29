# A Bernoulli-harmonic-zeta identity for the free scalar on hyperbolic space

## Abstract

For every natural number k, the combination of harmonic numbers, Bernoulli numbers and values of the Riemann zeta function at the non-positive integers displayed as eq. (C.12) of T. Nishioka and Y. Sato (arXiv:2101.02399, JHEP 05 (2021) 074) vanishes. The authors checked it numerically up to k = 100 and wrote that they do not know a proof; they use it to simplify the derivative of the spectral zeta function of a conformally coupled free scalar on even-dimensional hyperbolic space. That use is not formalized here: the statement below is the identity itself.

**Definition 1.1 (The identity).**

$$claim \Leftrightarrow (\forall k \in \mathbb{N},\; -(\frac{2^{-(2 \cdot k + 2)}}{k + 1}) \cdot \operatorname{harmonic}\left(2 \cdot k + 1\right) - (\sum_{m \in \operatorname{Icc}\left(1, k\right)} \frac{2^{-(2 \cdot k + 2)} \cdot (2^{2 \cdot m} - 2)}{k - m + 1} \cdot (\frac{\operatorname{bernoulli}\left(2 \cdot m\right)}{2 \cdot m})) + (\sum_{j \in \operatorname{range}\left(2 \cdot k + 2\right)} \frac{(-1)^{j}}{2^{2 \cdot k - j}} \cdot \operatorname{choose}\left(2 \cdot k + 1, j\right) \cdot \operatorname{harmonic}\left(j\right) \cdot \operatorname{riemannZeta}\left(-j\right)) + (1 - 2^{-(2 \cdot k + 1)}) \cdot \operatorname{harmonic}\left(2 \cdot k + 1\right) \cdot (\frac{\operatorname{bernoulli}\left(2 \cdot k + 2\right)}{k + 1}) = 0)$$

*Formalization.* `D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.claim` (`✓ std3`).

*Citation.* Tatsuma Nishioka; Yoshiki Sato (2021). *Free energy and defect C-theorem in free scalar theory*. DOI: [10.1007/JHEP05(2021)074](https://doi.org/10.1007/JHEP05(2021)074). URL: <https://arxiv.org/abs/2101.02399v5>.

*Commentary.*

Eq. (C.12) of the paper, for every k. The sum over m runs over 1 <= m <= k (empty for k = 0) and the sum over j over range(2k + 2) = {0, ..., 2k + 1}. H_n is the harmonic number harmonic(n) = 1 + 1/2 + ... + 1/n (with H_0 = 0), B_n the Bernoulli number bernoulli(n) with B_1 = -1/2, and riemannZeta the Riemann zeta function, evaluated at -j; the rational numbers are read in the complex numbers. The exponents -(2k + 2), 2k - j and -(2k + 1) of 2 are integers, so 2^(2k - j) is 1/2^(j - 2k) for j > 2k.

**Theorem 1.2 (Proof of the identity).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.result` (`✓ std3`). ∎

*Resolves.* `Problems/nishioka-sato-2021-bernoulli-harmonic-zeta-identity` (proved) by `D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nishioka-sato-2021-bernoulli-harmonic-zeta-identity","declaration_gid":"D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Tatsuma Nishioka; Yoshiki Sato (2021). *Free energy and defect C-theorem in free scalar theory*. DOI: [10.1007/JHEP05(2021)074](https://doi.org/10.1007/JHEP05(2021)074). URL: <https://arxiv.org/abs/2101.02399v5>.

*Commentary.*

Replace riemannZeta(-j) by (-1)^j B_(j+1)/(j+1) and multiply by 2^(2k+2)(k+1); put N = 2k + 2 and b_m = sum over i of C(m, i) 2^i B_i. The exponential generating functions give b_m = (2 - 2^m) B_m, since e^t 2t/(e^(2t) - 1) = 2t/(e^t - 1) - 2t/(e^(2t) - 1); in particular b_m = 0 for odd m. The middle sum becomes the sum of b_i (1/i + 1/(N - i)) over 1 <= i <= N - 1, and the zeta sum becomes the sum of C(N, i) 2^i B_i H_(i-1) over 1 <= i <= N. Two harmonic-binomial identities, C(n, i)(H_n - H_i) = sum over j = 1..n of C(n - j, i)/j (by Pascal's rule and induction) and the transform of C(n, i) 2^i B_i / i into the sum of (b_j - 1)/j (by induction on n), rewrite the zeta sum through sums of b_i/i and b_(N-i)/i. These cancel against the middle sum, and what is left is -H_(N-1) - 1/N + H_N = 0 after b_N = (2 - 2^N) B_N is used.

## References

- Truth anchor: `D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.claim`
- Truth anchor: `D5/S3/Quantum/FockSpace/HyperbolicScalarZetaIdentity.result`
