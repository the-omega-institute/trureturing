# The skew-information endpoint formula fails

## Abstract

A regular symmetric operator monotone function has a skew-information integrand below both endpoint values, refuting the proposed formula for its least value.

**Definition 1.1 (The skew-information integrand).**

$$\forall f \in (\mathbb{R} \to \mathbb{R}),\; \forall x \in \mathbb{R},\; \left(F_{f}\right)\left(x\right) = \frac{(1 + x - \frac{f\left(0\right) \cdot (1 - x)^{2}}{2 \cdot f\left(x\right)})}{2 \cdot f\left(x\right)}$$

*Formalization.* `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.lambdaIntegrand` (`✓ std3`).

*Citation.* Sixia Yu; C. H. Oh (2013). *Robertson-Schrödinger Uncertainty Relation Refined by Skew Information*. URL: <https://arxiv.org/abs/1303.6404v1>.

*Commentary.*

Appendix 2 of Yu and Oh defines lambda_f as the least value of F_f(x) for x at least zero. Here F_f(x) denotes lambdaIntegrand(f,x). The scalar definition itself accepts every real function and every real x; admissibility is imposed separately.

**Definition 1.2 (Regular symmetric operator monotone functions).**

$$\forall f \in (\mathbb{R} \to \mathbb{R}),\; \operatorname{Admissible}\left(f\right) \Leftrightarrow ((\forall x \in \mathbb{R},\; (0 \le x) \Rightarrow (0 \le f\left(x\right))) \land ((\forall n \in \mathbb{N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\operatorname{PosSemidef}\left(A\right)) \Rightarrow ((\operatorname{PosSemidef}\left(B\right)) \Rightarrow ((A \le B) \Rightarrow (\operatorname{cfc}\left(f, A\right) \le \operatorname{cfc}\left(f, B\right))))) \land ((\forall x \in \mathbb{R},\; (0 < x) \Rightarrow (x \cdot f\left(\frac{1}{x}\right) = f\left(x\right))) \land ((f\left(1\right) = 1) \land (0 < f\left(0\right))))))$$

*Formalization.* `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.Admissible` (`✓ std3`).

*Citation.* Sixia Yu; C. H. Oh (2013). *Robertson-Schrödinger Uncertainty Relation Refined by Skew Information*. URL: <https://arxiv.org/abs/1303.6404v1>.

*Commentary.*

Yu and Oh consider functions nonnegative on the nonnegative real axis, operator monotone, symmetric, normalized and regular. Operator monotonicity means that f(A) is at most f(B) whenever A and B are positive semidefinite complex matrices of any finite size and A is at most B. The order is the Loewner order, and cfc(f,A) is the continuous functional calculus. The size n ranges over all natural numbers, including zero. Symmetry is required for every positive real x; normalization is f(1) = 1 and regularity is f(0) > 0.

**Definition 1.3 (The proposed least value).**

$$claim \Leftrightarrow (\forall f \in (\mathbb{R} \to \mathbb{R}),\; (\operatorname{Admissible}\left(f\right)) \Rightarrow (\operatorname{IsLeast}\left(\left\{\left(F_{f}\right)\left(x\right) \mid x \in [0, \infty)\right\}, \min\{1, \frac{1}{4 \cdot f\left(0\right)}\}\right)))$$

*Formalization.* `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.claim` (`✓ std3`).

*Citation.* Sixia Yu; C. H. Oh (2013). *Robertson-Schrödinger Uncertainty Relation Refined by Skew Information*. URL: <https://arxiv.org/abs/1303.6404v1>.

*Commentary.*

Appendix 2 conjectures that lambda_f = min{1, 1/(4f(0))} always holds. IsLeast(S,c) means that c belongs to S and is at most every element of S, so the formula asserts both attainment and the lower-bound property for every admissible f. The source obtains the endpoint upper bound from F_f(1) = 1 and F_f(0) = 1/(4f(0)); the conjecture asserts equality with that bound.

**Theorem 1.4 (An interior value below the endpoint bound).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/yu-oh-2013-skew-information-lambda-refutation` (refuted) by `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"yu-oh-2013-skew-information-lambda-refutation","declaration_gid":"D5/S3/Quantum/Information/SkewInformationLambdaRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Sixia Yu; C. H. Oh (2013). *Robertson-Schrödinger Uncertainty Relation Refined by Skew Information*. URL: <https://arxiv.org/abs/1303.6404v1>.

*Commentary.*

Take f(x) = (2/9)(1 + x) + (10/3)·x/(11x + 1) + (10/3)·x/(x + 11). For a,b > 0 and x at least zero, x/(ax + b) = 1/a − (b/a)(ax + b)⁻¹. Matrix inversion reverses order on positive definite matrices, so this identity makes each rational term operator monotone on positive semidefinite matrices of every finite size. Positive linear combinations and the affine term preserve that order. All three terms are nonnegative on the nonnegative real axis. Direct calculation gives f(0) = 2/9, f(1) = 1 and x f(1/x) = f(x) for x > 0: the two rational terms are exchanged by the symmetry and the affine term is fixed. Thus f is admissible. At x = 1/4, f(1/4) = 31/54 and F_f(1/4) = 7641/7688 < 1 = min{1, 9/8}. The proposed least value is therefore not a lower bound of the integrand, contradicting claim.

## References

- Truth anchor: `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.Admissible`
- Truth anchor: `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.lambdaIntegrand`
- Truth anchor: `D5/S3/Quantum/Information/SkewInformationLambdaRefutation.result`
- Dependency: [D5/S3/Fourier/PositiveFourierApproximationRefutation](../../Fourier/PositiveFourierApproximationRefutation.md)
