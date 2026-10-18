# Hirche's Arimoto information combining conjecture

## Abstract

Hirche's binary Arimoto information combining conjecture holds with threshold three halves on the full closed coordinate range.

C. Hirche, Rényi Bounds on Information Combining, ISIT 2020, arXiv:2004.14408v1, §IV-A, Conjecture IV.6: “There exists a value 1 < α̂ < 1.5783, such that k_α^A(k_α^A⁻¹(x) ∗ k_α^A⁻¹(y)) (47) is convex for 0 < α < 1 and concave for 1 < α ≤ α̂.” Equation (23) defines K_α^A(X|Y) = e^{((1−α)/α) H_α^A(X|Y)}. For binary X ~ {p, 1−p}, k_α^A(p) = K_α^A(X) = (p^α + (1−p)^α)^{1/α}; write k for this coordinate. The assertion concerns each coordinate separately. All powers in k and delta use Real.rpow. At alpha=1, k is constant and the inverse branch does not exist; this order is excluded.

O. Rioul and J. Béguinot, The role of Mrs. Gerber's Lemma for evaluating the information leakage of secret sharing schemes, Barron Festschrift (Springer), HAL hal-05074668v1, §4, p. 20, Proposition 1 and Remark 6, give the prior numerical statement of the threshold α̂ = 3/2. Their support is a numerical sign plot produced with SageMath (Figure 3); no proof is given there. See `D5/L/Entropy/rioulbeguinot2025informationcombining`.

**Definition 1.1 (Binary Arimoto coordinate).**

$$\forall alpha \in \mathbb{R},\; \forall p \in \mathbb{R},\; \operatorname{k}\left(alpha, p\right) = \left(p^{alpha} + \left(1 - p\right)^{alpha}\right)^{\frac{1}{alpha}}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.k` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

The probability domain of the inverse branch is [0,1/2].

**Definition 1.2 (Coordinate endpoint).**

$$\forall alpha \in \mathbb{R},\; \operatorname{delta}\left(alpha\right) = 2^{\frac{1 - alpha}{alpha}}$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.delta` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

The half-probability value of k is delta, and its zero-probability value is one.

**Definition 1.3 (Closed coordinate range).**

$$\forall alpha \in \mathbb{R},\; \operatorname{I}\left(alpha\right) = \operatorname{Icc}\left(\operatorname{min}\left(1, \operatorname{delta}\left(alpha\right)\right), \operatorname{max}\left(1, \operatorname{delta}\left(alpha\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.I` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

For every positive alpha different from one, k is a continuous bijection from [0,1/2] onto this interval.

**Definition 1.4 (Specified probability inverse).**

$$\forall alpha \in \mathbb{R},\; \forall x \in \mathbb{R},\; \operatorname{kInv}\left(alpha, x\right) = \operatorname{invFunOn}\left(\operatorname{k}\left(alpha\right), \operatorname{Icc}\left(0, \frac{1}{2}\right), x\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.kInv` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

Function.invFunOn specifies the branch. On I(alpha) it equals the existing Cachin entropy inverse at alpha log(x)/(1-alpha); this proves continuity using that inverse.

**Definition 1.5 (Binary convolution).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{star}\left(a, b\right) = a + b - 2 \cdot a \cdot b$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.star` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

This is the shared binary convolution bconv.

**Definition 1.6 (Arimoto combining map).**

$$\forall alpha \in \mathbb{R},\; \forall x \in \mathbb{R},\; \forall y \in \mathbb{R},\; \operatorname{G}\left(alpha, x, y\right) = \operatorname{k}\left(alpha, \operatorname{star}\left(\operatorname{kInv}\left(alpha, x\right), \operatorname{kInv}\left(alpha, y\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.G` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

The two inputs use the same specified inverse branch.

**Definition 1.7 (Complete threshold claim).**

$$claim = \exists alphaHat:\mathbb{R},1 < alphaHat \land \left(alphaHat < \frac{15783}{10000} \land \left(\left(\forall alpha \in \mathbb{R},\; 0 < alpha \Rightarrow \left(alpha < 1 \Rightarrow \left(\forall y \in \mathbb{R},\; y \in \operatorname{I}\left(alpha\right) \Rightarrow \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{I}\left(alpha\right), x \mapsto \operatorname{G}\left(alpha, x, y\right)\right)\right)\right)\right) \land \left(\forall alpha \in \mathbb{R},\; 1 < alpha \Rightarrow \left(alpha \le alphaHat \Rightarrow \left(\forall y \in \mathbb{R},\; y \in \operatorname{I}\left(alpha\right) \Rightarrow \operatorname{ConcaveOn}\left(\mathbb{R}, \operatorname{I}\left(alpha\right), x \mapsto \operatorname{G}\left(alpha, x, y\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.claim` (`✓ std3`).

*Citation.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

The claim quantifies over all real orders in both ranges and every y in the closed range I(alpha).

**Theorem 1.8 (Conjecture IV.6 with witness three halves).**

$$\exists alphaHat:\mathbb{R},1 < alphaHat \land \left(alphaHat < \frac{15783}{10000} \land \left(\left(\forall alpha \in \mathbb{R},\; 0 < alpha \Rightarrow \left(alpha < 1 \Rightarrow \left(\forall y \in \mathbb{R},\; y \in \operatorname{I}\left(alpha\right) \Rightarrow \operatorname{ConvexOn}\left(\mathbb{R}, \operatorname{I}\left(alpha\right), x \mapsto \operatorname{G}\left(alpha, x, y\right)\right)\right)\right)\right) \land \left(\forall alpha \in \mathbb{R},\; 1 < alpha \Rightarrow \left(alpha \le alphaHat \Rightarrow \left(\forall y \in \mathbb{R},\; y \in \operatorname{I}\left(alpha\right) \Rightarrow \operatorname{ConcaveOn}\left(\mathbb{R}, \operatorname{I}\left(alpha\right), x \mapsto \operatorname{G}\left(alpha, x, y\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.result` (`✓ std3`). ∎

*Resolves.* `Problems/hirche-2020-arimoto-information-combining-convexity` (proved) by `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hirche-2020-arimoto-information-combining-convexity","declaration_gid":"D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche (2020). *Rényi Bounds on Information Combining*. DOI: [10.48550/arXiv.2004.14408](https://doi.org/10.48550/arXiv.2004.14408). URL: <https://arxiv.org/abs/2004.14408v1>.

*Commentary.*

The witness is alphaHat=3/2, strictly between one and 15783/10000. The result proves closed-interval separate convexity for all 0<alpha<1 and separate concavity for all 1<alpha≤3/2.

Put psi(t)=k(alpha,(1-t)/2), c=(1-alpha)/alpha, and let f be the positive Cachin bias slope. Then psi=exp(c h), psi'=-c psi f, and the existing derivative certificate f'=f F/t gives the Arimoto elasticity E=F-c t f=A/(1+tT). The shared identity bconv_bias gives G(psi(t),psi(v))=psi(vt). Identifying T with tanh((alpha-1)s) at t=tanh(s), uniqueness of derivatives identifies E with the hyperbolic certificate. Thus E increases throughout both order ranges.

For fixed 0<v<1, the derivative ratio R(t)=v psi'(vt)/psi'(t) satisfies R'=v psi'(vt)(E(vt)-E(t))/(t psi'(t))≤0. The prefactor is positive because both slopes have the same nonzero sign. Below order one the inverse bias decreases, so the transported derivative increases and the slice is convex. Above one it increases, so the transported derivative decreases and the slice is concave. Continuity on the closed range extends these inequalities to its endpoints. At v=0 the slice is constant, and at v=1 it is the identity. No endpoint inverse derivative is assumed.

## References

- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.G`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.I`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.claim`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.delta`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.k`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.kInv`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.result`
- Truth anchor: `D5/S3/Entropy/RenyiCombining/HircheArimotoCombining.star`
- Dependency: [D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic](ArimotoHyperbolic.md)
- Dependency: [D5/S3/Entropy/RenyiCombining/HircheCachinCombiningConcavity](HircheCachinCombiningConcavity.md)
- Dependency: [D5/S3/Weil/Budget/LinearCayleyScaleFlow](../../Weil/Budget/LinearCayleyScaleFlow.md)
