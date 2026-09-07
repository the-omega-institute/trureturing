# Normalized Jensen Degree Lowering

## Abstract

Fixed theta-moment Jensen polynomials satisfy exact degree lowering.

**Definition 1.1 (Fixed even theta kernel).**

$$\forall x\in\mathbb{R}, K\left(x\right)=\sum'_{n\in\mathbb{N}} (4 \pi^{2} (n+1)^{4} \exp\left(\frac{9 |x|}{2}\right)-6 \pi (n+1)^{2} \exp\left(\frac{5 |x|}{2}\right)) \exp\left(-\pi (n+1)^{2} \exp\left(2 |x|\right)\right)$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K denotes sourceThetaKernel. The natural index starts at zero, so n+1 runs over the positive integers. Absolute value specifies the even extension of the positive half-line expression. The primed sum denotes Lean's totalized tsum; this definition asserts no convergence theorem.

**Definition 1.2 (Fixed density expression).**

$$\forall x\in\mathbb{R}, p\left(x\right)=\frac{K\left(x\right)}{\Re\left(xiReading\left(\frac{1}{2}\right)\right)}$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

p denotes sourceThetaDensity, with the real part of the frozen xiReading at one half as its exact denominator. Private checked consequences of xi_reading_conj identify that real part with the complex central value and identify the complex coercion of p with K divided by that value. No nonzero-denominator or probability-mass theorem is asserted.

**Definition 1.3 (Even density moments).**

$$\forall k\in\mathbb{N}, m_{2 k}=\int_{\mathbb{R}} x^{2 k} p\left(x\right)\,dx$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceThetaMoment(k) is m at index 2k. The integral is the real Lebesgue integral of x^(2k) times the displayed density. It uses Lean's totalized integral and does not assert integrability.

**Definition 1.4 (Fixed moment coefficients).**

$$\forall k\in\mathbb{N}, a_{k}=\frac{m_{2 k}}{(2 k)!}$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a denotes the fixed sequence sourceThetaCoefficient. Its denominator is (2k)!, not k!. No Taylor-coefficient correspondence or assertion that a at zero is one is used.

**Definition 1.5 (Canonical Jensen adapter).**

$$\forall b:\mathbb{N}\to\mathbb{R}, \forall d\in\mathbb{N}, N\left(b, d\right)=\operatorname{map}_{\mathbb{R}\to\mathbb{C}}\left(J\left(k\mapsto k! b_{k}, d, 0\right)\circ(\frac{1}{d} X)\right)$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(b,d) denotes normalizedJensen b d for any real coefficient sequence b. J is the frozen jensenPolynomial: its coefficients are choose(d,k) times gamma(n+k), for k from zero through d. Here gamma(k)=k!b(k), the shift is zero, and polynomial composition scales the variable by the real inverse of d. The final map is the coefficient embedding from real to complex polynomials. X is the polynomial indeterminate.

**Definition 1.6 (Independent finite source polynomial).**

$$\forall d\in\mathbb{N}, P_{d}=\sum_{k=0}^{d} \frac{descFactorial\left(d, k\right)}{d^{k}} a_{k} X^{k}$$

*Formalization.* `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceJensenPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P at index d denotes sourceJensenPolynomial d, defined independently by this finite sum in Complex[X]. descFactorial(d,k) is the natural falling factorial d(d-1)...(d-k+1), with value one at k=0; its quotient by d^k is the prescribed weight. Natural factors and real coefficients are coerced to Complex. The upper limit is exactly d.

**Theorem 1.7 (Exact canonical normalization).**

$$\forall b:\mathbb{N}\to\mathbb{R}, \forall d\in\mathbb{N}, 1\leq d\Rightarrow N\left(b, d\right)=\sum_{k=0}^{d} \frac{descFactorial\left(d, k\right)}{d^{k}} b_{k} X^{k}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen_eq_fallingFactorial_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real sequence and every natural d at least one, the canonical adapter equals the finite falling-factorial sum. The proof distributes composition and coefficient mapping and uses the exact identity descFactorial(d,k)=k! choose(d,k).

**Theorem 1.8 (Universal polynomial degree lowering).**

$$\begin{aligned}\forall b:\mathbb{N}\to\mathbb{R}, \forall d\in\mathbb{N}, 2\leq d\Rightarrow \\N\left(b, d\right)-\frac{1}{d} X N\left(b, d\right)'=N\left(b, d-1\right)\circ(\frac{d-1}{d} X)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen_degree_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is an equality of complex polynomials for every real sequence b. The prime denotes Polynomial.derivative and the circle denotes polynomial composition. Comparing coefficients reduces it to the falling-factorial recurrence, including the top index k=d and all indices beyond d. The degree bound makes both d and d-1 nonzero.

**Theorem 1.9 (Source and canonical polynomial equality).**

$$\forall d\in\mathbb{N}, 1\leq d\Rightarrow P_{d}=N\left(a, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceJensenPolynomial_eq_normalizedJensen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The independent literal source polynomial equals the canonical adapter at the fixed density-moment coefficient sequence. This is the preceding normalization theorem specialized to a and read in the reverse direction.

**Theorem 1.10 (Exact source degree lowering at every complex argument).**

$$\begin{aligned}\forall d\in\mathbb{N}, 2\leq d\Rightarrow \forall v\in\mathbb{C}, \\P_{d}\left(v\right)-\frac{v}{d} P_{d}'\left(v\right)=P_{d-1}\left(\frac{d-1}{d} v\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.source_jensen_degree_lowering` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P'(v) means Polynomial.derivative evaluated at v. The proof uses the named source-to-canonical equality at d and d-1, then evaluates the universal lowering identity at v. All subtraction of natural degrees is interpreted in Nat before coercion; d at least two supplies the required bounds. No root-reality, RH, positivity, analytic convergence, or exact polynomial-degree premise is imposed.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen_degree_lowering`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.normalizedJensen_eq_fallingFactorial_sum`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceJensenPolynomial`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceJensenPolynomial_eq_normalizedJensen`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaCoefficient`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaDensity`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaKernel`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.sourceThetaMoment`
- Truth anchor: `D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.source_jensen_degree_lowering`
- Dependency: [D5/S3/Zeros/Jensen/JensenPolynomialObstruction](JensenPolynomialObstruction.md)
- Dependency: [D5/S3/Zeros/Symmetry/ZetaConjugationCovariance](../Symmetry/ZetaConjugationCovariance.md)
