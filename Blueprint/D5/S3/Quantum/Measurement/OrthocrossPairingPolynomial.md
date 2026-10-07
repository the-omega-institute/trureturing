# Gaussian polynomials for orthocross pairings

## Abstract

Inverse-frame pairings can be expressed through Gaussian polynomials. Intersecting supports are detected by evaluation at one; disjoint supports are detected by the derivative at one.

**Definition 1.1 (The pairing polynomial).**

$$\forall d \in \mathbb{N}, \forall \alpha, \beta \in \operatorname{Idx}(d), P_{\alpha\beta}(X) = v_{\alpha}^{*} H_{d}(X) v_{\beta}$$

*Formalization.* `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dimension d is natural and alpha,beta are orthocross indices. The Gaussian coefficients of the vectors are 1 and i. The polynomial matrix H has diagonal X^(d-1)-i, upper entry (1-X)X^(d+j-k-1), and lower entry i(1-X)X^(j-k-1). Expanding the one- or two-element supports defines P_alpha,beta. X denotes the polynomial indeterminate.

**Theorem 1.2 (Nonzero pairing polynomials).**

$$\forall d \in \mathbb{N}, \forall \alpha, \beta \in \operatorname{Idx}(d), P_{\alpha\beta} \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluation at one gives (1-i) times the ordinary vector pairing. This is nonzero when the supports intersect. For disjoint supports, the derivative at one is the negative pairing with upper entry 1 and lower entry i. The order of the support indices and the vector phases prevent that value from vanishing. Thus the polynomial is nonzero for every pair.

**Theorem 1.3 (A uniform coefficient bound).**

$$\forall d \in \mathbb{N}, (hd: 2 \leq d) \Rightarrow \forall \alpha, \beta \in \operatorname{Idx}(d), \forall n \in \mathbb{N}, \operatorname{norm}_{\mathbb{Z}[i]}([X^{n}]P_{\alpha\beta}) \leq 16$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_coeff_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each matrix-entry polynomial has coefficients of modulus at most one. A vector pairing contains at most four such terms with Gaussian unit phases. The triangle inequality bounds the modulus by four and its square by sixteen.

**Theorem 1.4 (Nonvanishing at the geometric ratio).**

$$\forall d \in \mathbb{N}, (hd: 4 \leq d) \Rightarrow \forall \alpha, \beta \in \operatorname{Idx}(d), P_{\alpha\beta}(q_{d}) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_at_ratio_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For d at least four, the Gaussian denominator of q has norm 2d squared minus 2d plus one, which exceeds sixteen. Coprimality forces that denominator to divide the leading coefficient of a polynomial vanishing at q. The nonzero polynomial and the coefficient bound exclude this divisibility.

**Theorem 1.5 (The inverse pairing identity).**

$$\forall d \in \mathbb{N}, (hd: 2 \leq d) \Rightarrow \forall \alpha, \beta \in \operatorname{Idx}(d), P_{\alpha\beta}(q_{d}) = \frac{(1-q_{d})q_{d}^{(d: \mathbb{Z})-2}}{u_{d}} v_{\alpha}^{*} \operatorname{candidate}(d) v_{\beta}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_eval_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying the inverse matrix by (1-q)q^(d-2)/u removes all negative powers. The diagonal quotient and the conjugate coefficient phase give exactly the entries of H(q). Expanding the original vector supports then identifies P(q) with the scaled inverse-frame pairing.

**Theorem 1.6 (Nonvanishing in every dimension).**

$$\forall d \in \mathbb{N}, (hd: 2 \leq d) \Rightarrow \forall \alpha, \beta \in \operatorname{Idx}(d), P_{\alpha\beta}(q_{d}) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_eval_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The uniform Gaussian coefficient argument applies in dimension at least four. In dimensions two and three, q equals (4-3i)/5 and (12-5i)/13 respectively. Exact evaluation of the finite vector supports gives nonzero values.

**Theorem 1.7 (Nonzero inverse-frame pairings).**

$$\forall d \in \mathbb{N}, \forall \alpha, \beta \in \operatorname{Idx}(d), v_{\alpha}^{*} \omega_{d}^{-1} v_{\beta} \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.inverse_frame_pairing_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial evaluation identity and its nonzero value exclude a zero inverse-frame pairing. Dimension zero has no indices. Dimension one contains only the basis vector, whose pairing is the positive diagonal parameter. The conclusion also includes equal indices.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.inverse_frame_pairing_ne_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_at_ratio_ne_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_coeff_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_eval_ne_zero`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_eval_ratio`
- Truth anchor: `D5/S3/Quantum/Measurement/OrthocrossPairingPolynomial.pairingPolynomial_ne_zero`
- Dependency: [D5/S3/Quantum/Measurement/OrthocrossInverseFrame](OrthocrossInverseFrame.md)
