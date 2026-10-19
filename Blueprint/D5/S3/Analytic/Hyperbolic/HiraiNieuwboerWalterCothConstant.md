# The optimal hyperbolic cotangent constant

## Abstract

The optimal real coefficient in the Hirai–Nieuwboer–Walter hyperbolic cotangent inequality is one over the square root of two.

Hirai–Nieuwboer–Walter, arXiv:2303.04771v2, §5, Lemma 5.13 and Remark 5.14:

“Lemma 5.13. The constant C = √2 is such that for all a, b ∈ ℝ, one has |coth((a − b)/2) (a coth(a/2) − b coth(b/2))| ≤ C √(ab(a − b) coth(a/2) coth(b/2) coth((a − b)/2)).”

“Remark 5.14. We conjecture, based on numerical evidence, that the optimal constant in the above inequality is C = 1/√2.”

The source proves the coefficient √2 and conjectures the optimal coefficient 1/√2. The repository resolves that conjecture: the optimal constant in $\operatorname{abs}\left(\operatorname{cothR}\left(\frac{a - b}{2}\right) \cdot \left(a \cdot \operatorname{cothR}\left(\frac{a}{2}\right) - b \cdot \operatorname{cothR}\left(\frac{b}{2}\right)\right)\right) \le C \cdot \operatorname{sqrt}\left(a \cdot b \cdot \left(a - b\right) \cdot \operatorname{cothR}\left(\frac{a}{2}\right) \cdot \operatorname{cothR}\left(\frac{b}{2}\right) \cdot \operatorname{cothR}\left(\frac{a - b}{2}\right)\right)$ is C = 1/√2. The inputs are distinct nonzero real numbers. The assertion comprises the uniform inequality and a strict counterexample for every smaller real coefficient.

**Definition 1.1 (Real hyperbolic cotangent).**

$$\forall x \in \mathbb{R},\; \operatorname{cothR}\left(x\right) = \frac{\operatorname{cosh}\left(x\right)}{\operatorname{sinh}\left(x\right)}$$

*Formalization.* `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.cothR` (`✓ std3`).

*Citation.* Hiroshi Hirai, Harold Nieuwboer, and Michael Walter (2023). *Interior-point methods on manifolds: theory and applications*. DOI: [10.48550/arXiv.2303.04771](https://doi.org/10.48550/arXiv.2303.04771). URL: <https://arxiv.org/abs/2303.04771>.

*Commentary.*

The quotient specifies the real hyperbolic cotangent.

**Definition 1.2 (Absolute cotangent difference).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{lhs}\left(a, b\right) = \operatorname{abs}\left(\operatorname{cothR}\left(\frac{a - b}{2}\right) \cdot \left(a \cdot \operatorname{cothR}\left(\frac{a}{2}\right) - b \cdot \operatorname{cothR}\left(\frac{b}{2}\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.lhs` (`✓ std3`).

*Citation.* Hiroshi Hirai, Harold Nieuwboer, and Michael Walter (2023). *Interior-point methods on manifolds: theory and applications*. DOI: [10.48550/arXiv.2303.04771](https://doi.org/10.48550/arXiv.2303.04771). URL: <https://arxiv.org/abs/2303.04771>.

*Commentary.*

The absolute value is taken after multiplying by the cotangent of the half-difference.

**Definition 1.3 (Positive hyperbolic product).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{radicand}\left(a, b\right) = a \cdot b \cdot \left(a - b\right) \cdot \operatorname{cothR}\left(\frac{a}{2}\right) \cdot \operatorname{cothR}\left(\frac{b}{2}\right) \cdot \operatorname{cothR}\left(\frac{a - b}{2}\right)$$

*Formalization.* `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.radicand` (`✓ std3`).

*Citation.* Hiroshi Hirai, Harold Nieuwboer, and Michael Walter (2023). *Interior-point methods on manifolds: theory and applications*. DOI: [10.48550/arXiv.2303.04771](https://doi.org/10.48550/arXiv.2303.04771). URL: <https://arxiv.org/abs/2303.04771>.

*Commentary.*

On the permitted domain each factor x coth(x/2) is strictly positive.

**Definition 1.4 (The uniform estimate and optimality).**

$$claim = \left(\left(\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; a \ne 0 \Rightarrow \left(b \ne 0 \Rightarrow \left(a \ne b \Rightarrow \operatorname{lhs}\left(a, b\right) \le \frac{1}{\operatorname{sqrt}\left(2\right)} \cdot \operatorname{sqrt}\left(\operatorname{radicand}\left(a, b\right)\right)\right)\right)\right) \land \left(\forall C \in \mathbb{R},\; C < \frac{1}{\operatorname{sqrt}\left(2\right)} \Rightarrow \left(\exists a \in \mathbb{R},\; \exists b \in \mathbb{R},\; a \ne 0 \land \left(b \ne 0 \land \left(a \ne b \land C \cdot \operatorname{sqrt}\left(\operatorname{radicand}\left(a, b\right)\right) < \operatorname{lhs}\left(a, b\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.claim` (`✓ std3`).

*Citation.* Hiroshi Hirai, Harold Nieuwboer, and Michael Walter (2023). *Interior-point methods on manifolds: theory and applications*. DOI: [10.48550/arXiv.2303.04771](https://doi.org/10.48550/arXiv.2303.04771). URL: <https://arxiv.org/abs/2303.04771>.

*Commentary.*

The first conjunct includes both signs of both inputs. The second quantifies over every real coefficient strictly below 1/√2.

**Theorem 1.5 (Optimal coefficient one over square root two).**

$$\left(\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; a \ne 0 \Rightarrow \left(b \ne 0 \Rightarrow \left(a \ne b \Rightarrow \operatorname{lhs}\left(a, b\right) \le \frac{1}{\operatorname{sqrt}\left(2\right)} \cdot \operatorname{sqrt}\left(\operatorname{radicand}\left(a, b\right)\right)\right)\right)\right) \land \left(\forall C \in \mathbb{R},\; C < \frac{1}{\operatorname{sqrt}\left(2\right)} \Rightarrow \left(\exists a \in \mathbb{R},\; \exists b \in \mathbb{R},\; a \ne 0 \land \left(b \ne 0 \land \left(a \ne b \land C \cdot \operatorname{sqrt}\left(\operatorname{radicand}\left(a, b\right)\right) < \operatorname{lhs}\left(a, b\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.result` (`✓ std3`). ∎

*Resolves.* `Problems/hirai-nieuwboer-walter-2023-coth-constant` (proved) by `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hirai-nieuwboer-walter-2023-coth-constant","declaration_gid":"D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hiroshi Hirai, Harold Nieuwboer, and Michael Walter (2023). *Interior-point methods on manifolds: theory and applications*. DOI: [10.48550/arXiv.2303.04771](https://doi.org/10.48550/arXiv.2303.04771). URL: <https://arxiv.org/abs/2303.04771>.

*Commentary.*

The estimate holds at 1/√2, and every smaller real coefficient admits distinct nonzero real inputs with a strict reverse inequality.

Extend u(x)=x coth(x) by u(0)=1 and put ψ(x)=x tanh(x). The function u is even, at least one, nondecreasing and 1-Lipschitz on the nonnegative half-line. The function ψ is even and nondecreasing there, and u(x)ψ(x)=x². For A=max(|x|,|y|), B=min(|x|,|y|), δ=A−B and D=|x−y|, the Lipschitz bound gives (u(x)−u(y))²≤δ²=ψ(δ)u(δ)≤ψ(D)u(A)u(B). The substitutions a=2x and b=2y turn this into the squared ratio bound 1/2.

For C<1/√2, choose t=2/(1−C√2)>0. Since u(t)≥t, u(t)−1−Ct√2≥1>0. The continuous function F(y)=u(t−y)(u(t)−u(y))−C(t−y)√(2u(t)u(y)u(t−y)) is strictly positive at y=0. It remains positive for some small y with 0<y<t. The pair a=2t, b=2y is then a strict violation at coefficient C, proving sharpness. Through the paper's Theorem 5.15, the scalar estimate gives the consequence “squared distance on PD(n) is 8-self-concordant”; this geometric consequence is not formalized here.

## References

- Truth anchor: `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.claim`
- Truth anchor: `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.cothR`
- Truth anchor: `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.lhs`
- Truth anchor: `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.radicand`
- Truth anchor: `D5/S3/Analytic/Hyperbolic/HiraiNieuwboerWalterCothConstant.result`
- Dependency: [D5/S3/Entropy/RenyiCombining/ArimotoHyperbolic](../../Entropy/RenyiCombining/ArimotoHyperbolic.md)
- Dependency: [D5/S3/Observer/Fluctuation/ThermalCoefficientFloor](../../Observer/Fluctuation/ThermalCoefficientFloor.md)
- Dependency: [D5/S3/Weil/Budget/LinearCayleyScaleFlow](../../Weil/Budget/LinearCayleyScaleFlow.md)
