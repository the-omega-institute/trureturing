# MABK self-testing positivity for the two remaining blocks

## Abstract

The five-term MABK self-testing expression is nonnegative throughout the real cube for every n >= 6 and either of the two small index blocks h = 1, 2.

**Definition 1.1 (The cube endpoint).**

$$kappa = 1 - \frac{1}{\sqrt{2}}$$

*Formalization.* `D5/S3/QuantumBounds/MabkSelfTestingPositivity.kappa` (`✓ std3`).

*Citation.* Shen Cao; Xingjian Zhang; Fei Shi; Qi Zhao (2026). *Size-Independent Robustness in Multipartite Bell Self-Testing*. DOI: [10.48550/arXiv.2608.30851](https://doi.org/10.48550/arXiv.2608.30851). URL: <https://arxiv.org/abs/2608.30851v1>.

*Commentary.*

The endpoint is kappa = 1 - 1/sqrt(2), as in the Supplemental Material. All divisions in this document are real divisions.

**Definition 1.2 (The source expression).**

$$\forall n \in \mathbb{N},\; \forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall v \in \operatorname{Fin}\left(n\right)\to\mathbb{R},\; \operatorname{lambdaA}\left(n, T, v\right) = 1 + (\frac{1 + \sqrt{2}}{\sqrt{2}})^{n} \cdot \prod_{j \in \operatorname{Fin}\left(n\right)} (\operatorname{v}\left(j\right) \cdot \left(1 - \frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right)\right)) + \sqrt{2} \cdot (\prod_{j \in T} (1 - \frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right)) \cdot \prod_{j \in T^{\mathrm{c}}} (\frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right)) + \prod_{j \in T} (\frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right)) \cdot \prod_{j \in T^{\mathrm{c}}} (1 - \frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right))) - (\sqrt{2} + 1)^{2} \cdot (\prod_{j \in T} ((1 - \operatorname{v}\left(j\right))^{2}) \cdot \prod_{j \in T^{\mathrm{c}}} (\operatorname{v}\left(j\right) \cdot \left(2 - \operatorname{v}\left(j\right)\right)) + \prod_{j \in T} (\operatorname{v}\left(j\right) \cdot \left(2 - \operatorname{v}\left(j\right)\right)) \cdot \prod_{j \in T^{\mathrm{c}}} ((1 - \operatorname{v}\left(j\right))^{2})) + (2 + \sqrt{2}) \cdot (\prod_{j \in T} (\left(1 - \frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right)\right) \cdot \left(1 - \operatorname{v}\left(j\right)\right)) \cdot \prod_{j \in T^{\mathrm{c}}} (\frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right) \cdot \sqrt{2 \cdot \operatorname{v}\left(j\right) - (\operatorname{v}\left(j\right))^{2}}) + \prod_{j \in T} (\frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right) \cdot \sqrt{2 \cdot \operatorname{v}\left(j\right) - (\operatorname{v}\left(j\right))^{2}}) \cdot \prod_{j \in T^{\mathrm{c}}} (\left(1 - \frac{1 + \sqrt{2}}{\sqrt{2}} \cdot \operatorname{v}\left(j\right)\right) \cdot \left(1 - \operatorname{v}\left(j\right)\right)))$$

*Formalization.* `D5/S3/QuantumBounds/MabkSelfTestingPositivity.lambdaA` (`✓ std3`).

*Citation.* Shen Cao; Xingjian Zhang; Fei Shi; Qi Zhao (2026). *Size-Independent Robustness in Multipartite Bell Self-Testing*. DOI: [10.48550/arXiv.2608.30851](https://doi.org/10.48550/arXiv.2608.30851). URL: <https://arxiv.org/abs/2608.30851v1>.

*Commentary.*

The five terms are the displayed lambda expression in the Supplemental Material, Efficient Verification of Optimal Lower Bound, PDF p. 37. The source indices 1,...,n are encoded by Fin n through i -> i + 1. T is the source block T_a, and its complement T^c is the block P_a. Every product is a finite product over its displayed index set; v is real-valued. Lean's real square root is total and returns zero on negative arguments; the radicands are nonnegative on the stated cube.

**Definition 1.3 (The conjectured non-negativity).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; (6 \le n) \Rightarrow (\forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; ((\operatorname{card}\left(T\right) = 1) \lor (\operatorname{card}\left(T\right) = 2)) \Rightarrow (\forall v \in \operatorname{Fin}\left(n\right)\to\mathbb{R},\; (\forall i \in \operatorname{Fin}\left(n\right),\; (0 \le \operatorname{v}\left(i\right)) \land (\operatorname{v}\left(i\right) \le kappa)) \Rightarrow (0 \le \operatorname{lambdaA}\left(n, T, v\right)))))$$

*Formalization.* `D5/S3/QuantumBounds/MabkSelfTestingPositivity.claim` (`✓ std3`).

*Citation.* Shen Cao; Xingjian Zhang; Fei Shi; Qi Zhao (2026). *Size-Independent Robustness in Multipartite Bell Self-Testing*. DOI: [10.48550/arXiv.2608.30851](https://doi.org/10.48550/arXiv.2608.30851). URL: <https://arxiv.org/abs/2608.30851v1>.

*Commentary.*

The Supplemental Material, PDF p. 39, states verbatim: “For n ≤ 5 this bound is already established analytically [20, 23]; for n ≥ 6 the two remaining cases (h = 1, 2) are an open conjecture supported by the numerical evidence above.” The encoded assertion is non-negativity of the displayed lambda expression at every point of [0,kappa]^n. The condition h <= d holds automatically for n >= 6 and h in {1,2}; h = card(T) and d = card(T^c).

**Theorem 1.4 (Positivity on the whole cube).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/MabkSelfTestingPositivity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Shen Cao; Xingjian Zhang; Fei Shi; Qi Zhao (2026). *Size-Independent Robustness in Multipartite Bell Self-Testing*. DOI: [10.48550/arXiv.2608.30851](https://doi.org/10.48550/arXiv.2608.30851). URL: <https://arxiv.org/abs/2608.30851v1>.

*Commentary.*

Write r = sqrt(2), x_i = 1 - v_i, y_i = sqrt(2 v_i - v_i^2), a_i = 1 - ((1+r)/r)v_i and b_i = ((1+r)/r)v_i. The coordinate bounds give a_i >= x_i^2, b_i <= 1/2, y_i^2 <= 1/2 and x_i^2+y_i^2=1. For the complementary block J, let q be the product of x_i, d = card(J), B = product_T b_i, Y = product_T y_i and s = 1+r. A finite-product induction gives (product_J y_i)^2 <= (1-q^2) 2^{1-d}. Set K=(2+r)BY, C=1-K/2-s^2 2^{1-d} and F=1-s^2 Y^2+rB+K. Keeping the positive cubic term and using 2q^3 >= 3q^2-1 gives the lower bound C(1-q^2)+Fq^2. For h=1, F is nonnegative by factorization on the unit circle; the certificate is the denominator-cleared version of the factorization with t=y/(1+x). For h=2, F is bounded below by 1-(5/2+13r/8)Y^2+(5/4+7r/8)Y^3 for 0 <= Y <= 1/2, which is at least (34-19r)/64 > 0. The block-size bounds make C nonnegative in both cases. This proves the scalar conjecture; the Bell-operator reductions and the extractability conclusions of the source are outside this module.

## References

- Truth anchor: `D5/S3/QuantumBounds/MabkSelfTestingPositivity.claim`
- Truth anchor: `D5/S3/QuantumBounds/MabkSelfTestingPositivity.kappa`
- Truth anchor: `D5/S3/QuantumBounds/MabkSelfTestingPositivity.lambdaA`
- Truth anchor: `D5/S3/QuantumBounds/MabkSelfTestingPositivity.result`
