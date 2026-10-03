# The inverse Gram matrix of an orthocross MIC is half-integral

## Abstract

For every dimension d and every orthonormal basis of C^d, the Gram matrix G of the orthocross MIC is invertible and every entry of G^(-1) is an integer or a half-integer. This proves the conjecture of J. B. DeBrota, C. A. Fuchs and B. C. Stacey (arXiv:1812.08762), who observed it numerically.

**Definition 1.1 (Basis and cross vectors).**

$$\operatorname{vec}\left(X_{j}\right) = e_{j},\qquad\operatorname{vec}\left(T_{jk}\right) = e_{j} + e_{k},\qquad\operatorname{vec}\left(V_{jk}\right) = e_{j} + i \cdot e_{k}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.vec` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

The index set consists of the d basis indices X_j and, for every pair j < k, a real cross index T_jk and an imaginary cross index V_jk, d^2 indices in all. The vectors are e_j, e_j + e_k and e_j + i e_k.

**Definition 1.2 (Normalising weights).**

$$\operatorname{weight}\left(X_{j}\right) = 1,\qquad\operatorname{weight}\left(T_{jk}\right) = \operatorname{weight}\left(V_{jk}\right) = \frac{1}{2}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.weight` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

The weight is 1 for a basis vector and 1/2 for a cross vector, whose squared norm is 2, so that w(alpha) v_alpha v_alpha^* is a rank-one projector.

**Definition 1.3 (The projectors Pi_alpha).**

$$\operatorname{proj}\left(U, \alpha\right) = \operatorname{weight}\left(\alpha\right) \cdot (U \operatorname{vec}\left(\alpha\right)) (U \operatorname{vec}\left(\alpha\right))^{*}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.proj` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

For a unitary U, the columns U e_j form the chosen orthonormal basis, and Pi_alpha(U) is the projector onto U v_alpha: the paper's Gamma_jj, (1/2)(|j> + |k>)(<j| + <k|) and (1/2)(|j> + i|k>)(<j| - i<k|) for j < k.

**Definition 1.4 (The frame operator Omega).**

$$\operatorname{frame}\left(U\right) = \sum_{\alpha} \operatorname{proj}\left(U, \alpha\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.frame` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

Omega is the sum of the d^2 projectors.

**Definition 1.5 (The orthocross MIC elements).**

$$\operatorname{mic}\left(U, \alpha\right) = \operatorname{frame}\left(U\right)^{-\frac{1}{2}} \operatorname{proj}\left(U, \alpha\right) \operatorname{frame}\left(U\right)^{-\frac{1}{2}}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.mic` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

E_alpha = Omega^(-1/2) Pi_alpha Omega^(-1/2), where Omega^(-1/2) is the positive square root of the inverse of the positive definite matrix Omega.

**Definition 1.6 (The Gram matrix).**

$$\operatorname{gram}\left(U, \alpha, \beta\right) = \operatorname{tr}\left(\operatorname{mic}\left(U, \alpha\right) \operatorname{mic}\left(U, \beta\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.gram` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

The Gram matrix of the MIC, G_alpha beta = tr(E_alpha E_beta).

**Definition 1.7 (The conjecture).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; \forall U \in \operatorname{UnitaryGroup}\left(d\right),\; (\operatorname{IsUnit}\left(\operatorname{det}\left(\operatorname{gram}\left(U\right)\right)\right)) \land (\forall a \in \operatorname{Idx}\left(d\right),\; \forall b \in \operatorname{Idx}\left(d\right),\; \exists z \in \mathbb{Z},\; 2 \cdot (\operatorname{gram}\left(U\right)^{-1})(a, b) = z))$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.claim` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

The conjecture of the paper, for every dimension d and every orthonormal basis (every unitary U): G is invertible and 2 (G^(-1))_ab is an integer for all indices a and b of Idx(d), the d^2 indices X_j, T_jk and V_jk.

**Theorem 1.8 (Half-integrality of the inverse Gram matrix).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.result` (`✓ std3`). ∎

*Resolves.* `Problems/debrota-2020-orthocross-gram-inverse-half-integer` (proved) by `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"debrota-2020-orthocross-gram-inverse-half-integer","declaration_gid":"D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

Since the square of Omega^(-1/2) is Omega^(-1), G_alpha beta = tr(Pi_alpha Omega^(-1) Pi_beta Omega^(-1)), and a unitary change of basis does not change it, so U = 1 suffices. In the standard basis Omega has d on the diagonal, (1 - i)/2 above it and (1 + i)/2 below it. The matrices D_T = E_jk + E_kj, D_V = i(E_kj - E_jk) and D_X = E_jj - E_jj C - C E_jj, where C is the off-diagonal part of Omega, satisfy tr(D_alpha Pi_beta) = delta_alpha beta; there are d^2 of them and they are linearly independent, so every matrix Y equals the sum over beta of tr(Y Pi_beta) D_beta. It follows that G M = 1 for M_beta gamma = tr(D_beta Omega D_gamma Omega), so G is invertible and G^(-1) = M. The matrices (1 - i) Omega and (1 - i) D_alpha have Gaussian-integer entries, and 4 = (1 + i) i (1 - i)^3, so every entry of 4 Z with Z = Omega D_gamma Omega is (1 + i) times a Gaussian integer a + b i. Z is Hermitian, so M_T gamma = Z_kj + Z_jk, M_V gamma = i Z_jk - i Z_kj and M_X gamma = Z_jj minus the sum over q of C_jq Z_qj + C_qj Z_jq are read off from these entries, and in each case 2M is an integer: a - b, -(a + b), and a sum of the integers a or -b with 2 Z_jj.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.frame`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.gram`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.mic`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.proj`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.result`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.vec`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger.weight`
