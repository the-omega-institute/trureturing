# Source Jensen Integral Extension

## Abstract

Adjacent source Jensen polynomials differ by one exact integration constant.

**Theorem 1.1 (The primitive and its constant).**

$$\begin{gathered}\forall d\ge2,\quad {q_{d}}_{\mathbb{C}}=\operatorname{reflect}_{d}(P_{d}(-X)),\quad \forall x\in\mathbb{R},q_{d}'(x)=d\alpha_{d}^{d-1}q_{d-1}(\frac{x}{\alpha_{d}}),\\q_{d}(0)=\beta_{d},\quad \forall x\in\mathbb{R},q_{d}(x)=R_{d}(x)+\beta_{d},\\\forall b,x\in\mathbb{R},q_{d,b}=q_{d}+b-\beta_{d},\quad q_{d,b}'=q_{d}',\quad q_{d,b}(x)=R_{d}(x)+b,\\(q_{d,b}(x)=0\iff R_{d}(x)=-b),\quad \forall x\in\mathbb{R},\exists b_{0},b_{1}\in\mathbb{R},q_{d,b_{0}}(x)=0\land q_{d,b_{1}}(x)\neq0\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceJensenIntegralExtension.source_jensen_integral_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d at least two, P is the real finite source polynomial with coefficients (d)_k a_k/d^k, where a_k is the frozen sourceThetaCoefficient k. Q is Polynomial.reflect d applied to P(-X). The theorem identifies its complexification with the reflection of the actual sourceJensenPolynomial, so Q is defined at zero as a polynomial.

$\alpha_{d}=\frac{d-1}{d},\quad \beta_{d}=(-1)^{d}\frac{d!}{d^{d}}a_{d},\quad R_{d}(x)=\int_{0}^{x}d\alpha_{d}^{d-1}q_{d-1}(\frac{u}{\alpha_{d}})\, du$

Every x and every replacement constant b in the formulas is real. The integral is oriented from zero to x; negative x and zero are included. Write Q_b = Q + b - beta. Its derivative is unchanged, its value is R(x)+b, and its roots satisfy R(x)=-b. The two symbolic constants -R(x) and 1-R(x) respectively include and exclude the chosen x from the real zero set. This concerns the family obtained by replacing the constant; the actual theta constant remains fixed. No assertion of computational ease or of a real-rooted theta tower follows.

The proof binds the frozen Jensen degree-lowering identity through Polynomial.coeff_reflect and applies Mathlib's fundamental theorem of calculus. The remaining equalities are coefficient, field, and ring normalization; there is no finite enumeration or new analytic estimate.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/SourceJensenIntegralExtension.source_jensen_integral_extension`
- Dependency: [D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering](NormalizedJensenDegreeLowering.md)
