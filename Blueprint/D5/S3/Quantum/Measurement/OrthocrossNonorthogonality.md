# Inverse-frame pairings of orthocross measurements

## Abstract

Orthocross Gram entries are weighted squared moduli of inverse-frame pairings. Every entry is strictly positive, and all entries tend uniformly to zero as the dimension increases.

**Definition 1.1 (Nonorthogonality and uniform decay).**

$$claim := (\forall d \in \mathbb{N}, \forall U \in \operatorname{unitaryGroup}(\operatorname{Fin}(d), \mathbb{C}), \forall \alpha, \beta \in \operatorname{Idx}(d), (hab: \alpha \neq \beta) \Rightarrow 0 < G_{\alpha\beta}(U)) \land (\forall \varepsilon \in \mathbb{R}, (he: 0 < \varepsilon) \Rightarrow \exists d_{0} \in \mathbb{N}, \forall d \in \mathbb{N}, (hd: d_{0} \leq d) \Rightarrow \forall U \in \operatorname{unitaryGroup}(\operatorname{Fin}(d), \mathbb{C}), \forall \alpha, \beta \in \operatorname{Idx}(d), \Vert G_{\alpha\beta}(U)\Vert < \varepsilon)$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.claim` (`✓ std3`).

*Citation.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

The dimension d is any natural number, U is any unitary d by d complex matrix, and alpha and beta run over the basis, real cross and imaginary cross indices. Strict complex positivity means a strictly positive real value. The second clause is uniform in both the basis and the indices. The inverse-frame pairing identity connects strict positivity to nonvanishing of the vector pairings.

**Theorem 1.2 (Weighted squared modulus).**

$$\forall d \in \mathbb{N}, \forall U \in \operatorname{unitaryGroup}(\operatorname{Fin}(d), \mathbb{C}), \forall \alpha, \beta \in \operatorname{Idx}(d), G_{\alpha\beta}(U) = w_{\alpha} w_{\beta} \operatorname{ofReal}(\Vert v_{\alpha}^{*} \omega_{d}^{-1} v_{\beta}\Vert^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.gram_eq_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Omega is the standard-basis frame. Unitary covariance reduces each Gram entry to tr(Pi_alpha M Pi_beta M). Multiplication of the two rank-one projectors gives the product of the inverse-frame pairing and its complex conjugate, because M is Hermitian. The weights are 1 for basis indices and 1/2 for cross indices.

**Theorem 1.3 (A lower bound for the frame).**

$$\forall d \in \mathbb{N}, \frac{(d: \mathbb{R})}{4} I_{d} \leq \omega_{d}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.frame_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

The standard-basis frame has d on the diagonal and (1 - i)/2 or (1 + i)/2 away from the diagonal. Every off-diagonal modulus is at most 3/4. Gershgorin's theorem applied after subtracting (d/4)I shows that every eigenvalue of the difference is nonnegative.

**Theorem 1.4 (An operator norm bound for the inverse).**

$$\forall d \in \mathbb{N}, (hd: 0 < d) \Rightarrow \Vert \omega_{d}^{-1}\Vert \leq \frac{4}{(d: \mathbb{R})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.inverse_frame_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

In positive dimension, inverse order reverses the frame lower bound. The inverse is positive semidefinite, so its operator norm is at most 4/d.

**Theorem 1.5 (A bound for every Gram entry).**

$$\forall d \in \mathbb{N}, (hd: 0 < d) \Rightarrow \forall U \in \operatorname{unitaryGroup}(\operatorname{Fin}(d), \mathbb{C}), \forall \alpha, \beta \in \operatorname{Idx}(d), \Vert G_{\alpha\beta}(U)\Vert \leq \frac{256}{(d: \mathbb{R})^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.gram_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

Each unnormalised orthocross vector has Euclidean norm at most two. Cauchy-Schwarz and the inverse norm bound give pairing modulus at most 16/d. The weights are at most one, and the squared-modulus identity therefore bounds every Gram entry by 256 divided by d squared, uniformly in the basis and indices.

**Theorem 1.6 (Uniform decay with dimension).**

$$\forall \varepsilon \in \mathbb{R}, (he: 0 < \varepsilon) \Rightarrow \exists d_{0} \in \mathbb{N}, \forall d \in \mathbb{N}, (hd: d_{0} \leq d) \Rightarrow \forall U \in \operatorname{unitaryGroup}(\operatorname{Fin}(d), \mathbb{C}), \forall \alpha, \beta \in \operatorname{Idx}(d), \Vert G_{\alpha\beta}(U)\Vert < \varepsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.gram_uniform_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

Choose a natural number larger than both 1 and 256/epsilon. For every dimension at least that number, the uniform Gram bound is strictly less than epsilon. This establishes the second clause of the assertion.

**Theorem 1.7 (Strict positivity of every Gram entry).**

$$\forall d \in \mathbb{N}, \forall U \in \operatorname{unitaryGroup}(\operatorname{Fin}(d), \mathbb{C}), \forall \alpha, \beta \in \operatorname{Idx}(d), 0 < G_{\alpha\beta}(U)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.gram_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

Every inverse-frame pairing is nonzero. Its squared modulus is strictly positive, and both orthocross weights are positive. The weighted squared-modulus identity therefore gives strict complex positivity, which means that the entry is a strictly positive real number. This includes equal indices.

**Theorem 1.8 (Positivity and uniform decay).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.result` (`✓ std3`). ∎

*Resolves.* `Problems/debrota-2020-orthocross-nonorthogonality` (proved) by `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"debrota-2020-orthocross-nonorthogonality","declaration_gid":"D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey (2020). *The Varieties of Minimal Tomographically Complete Measurements*. DOI: [10.1142/S0219749920400055](https://doi.org/10.1142/S0219749920400055). URL: <https://arxiv.org/abs/1812.08762v5>.

*Commentary.*

Strict positivity of every entry implies the first clause for distinct indices. The uniform decay bound supplies the second clause. Both hold for every dimension and every unitary basis; dimension zero has an empty index set. The proof uses the closed geometric inverse and the Gaussian rational-root obstruction for its pairing polynomials.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.claim`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.frame_lower_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.gram_eq_norm_sq`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.gram_norm_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.gram_pos`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.gram_uniform_decay`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.inverse_frame_norm_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossNonorthogonality.result`
- Dependency: [D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial](OrthocrossPairingPolynomial.md)
