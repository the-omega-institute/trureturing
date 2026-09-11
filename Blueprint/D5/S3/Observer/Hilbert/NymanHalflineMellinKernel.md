# Half-Line Mellin Kernel

## Abstract

The exact Mellin separator kernel and dual norm on the positive half-line.

Work in H=Lp(C,2,volume restricted to (0,infinity)). Let beta=Re(rho)>1/2 and rho differ from one. Positive real bases use the principal complex power. The kernel is conjugated because the first argument of the complex inner product is conjugate-linear.

**Definition 1.1 (Real source vector).**

$$\forall a\in \mathbb{R}, a\ge 1, F_{a}\in H$$

*Formalization.* `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F_a is the Lp class of x |-> ofReal(fract(1/(a*x))). The construction proves square integrability before taking the quotient.

**Theorem 1.2 (Actual representative).**

$$\forall a\in \mathbb{R}, a\ge 1, F_{a}(x)=\operatorname{fract}(\frac{1}{ax})\quad\mathrm{a.e.} (0,\infty)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector_coe_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality is almost everywhere for positiveMeasure. Real values are embedded into C, and the measure and exponent remain those of H.

**Theorem 1.3 (Natural sources agree).**

$$\forall n\in \mathbb{N},n\ge 1,F_{n}=\operatorname{sourceVector}(n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector_nat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality in the Lp quotient identifies the real-parameter construction with the original natural source family, including n=1.

**Theorem 1.4 (Reciprocal tail).**

$$\forall a\in \mathbb{R}, a\ge 1, \forall x\in \mathbb{R},x> 1\Rightarrow \operatorname{fract}(\frac{1}{ax})=\frac{1}{ax}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Since 0 < 1/(a*x) < 1 on this tail, taking fractional part changes nothing. This is a pointwise identity for every real a at least one.

**Definition 1.5 (Kernel vector).**

$$\forall \rho\in \mathbb{C},\beta=\Re \rho> \frac{1}{2},\rho\neq1, k_{\rho}\in H$$

*Formalization.* `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The near-zero piece has square norm x^(2*beta-2); the tail has square norm norm(rho-1)^(-2)*x^(-2). Their integrability constructs the Lp vector.

**Theorem 1.6 (Conjugated representative).**

$$\forall \rho\in \mathbb{C},\beta=\Re \rho> \frac{1}{2},\rho\neq1, k_{\rho}(x)=1_{(0,1)}(x)\overline{x^{\rho-1}}-1_{(1,\infty)}(x)\frac{\overline{(\rho-1)^{-1}}}{x}\quad\mathrm{a.e.}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineKernel_coe_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This representative identity is almost everywhere for positiveMeasure. The two open intervals are disjoint; values at endpoints have measure zero.

**Theorem 1.7 (Exact kernel energy).**

$$\forall \rho\in \mathbb{C},\beta=\Re \rho> \frac{1}{2},\rho\neq1, \Vert k_{\rho}\Vert ^{2}=\frac{1}{2\beta-1}+\frac{1}{\Vert \rho-1\Vert ^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineKernel_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Disjoint support makes the square norm a sum. The power integral over (0,1) is 1/(2*beta-1); the integral of x^(-2) over (1,infinity) is one.

**Definition 1.8 (Continuous complex-linear functional).**

$$\forall \rho\in \mathbb{C},\beta=\Re \rho> \frac{1}{2},\rho\neq1, \forall f\in H,J_{\rho}(f)=\langle k_{\rho},f\rangle$$

*Formalization.* `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineFunctional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Riesz inner-product map defines J as a continuous C-linear map from H to C.

**Theorem 1.9 (Representative-independent integral formula).**

$$\forall \rho\in \mathbb{C},\beta=\Re \rho> \frac{1}{2},\rho\neq1, \forall f\in H,\forall g:\mathbb{R}\to \mathbb{C},g=_{\mathrm{a.e.}}f\Rightarrow \begin{gathered}\operatorname{IntegrableOn}((x\mapsto g(x)x^{\rho-1}),(0,1))\\\land \operatorname{IntegrableOn}((x\mapsto \frac{g(x)}{x}),(1,\infty))\\\land J_{\rho}(f)=\int_{0}^{1}g(x)x^{\rho-1}\,dx-(\rho-1)^{-1}\int_{1}^{\infty}\frac{g(x)}{x}\,dx\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineFunctional_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every g equal to the Lp representative almost everywhere for positiveMeasure, g(x)*x^(rho-1) is integrable on (0,1), and g(x)/x is integrable on (1,infinity). The displayed identity holds for every such g, so it is independent of the chosen representative. Cauchy-Schwarz gives integrability, and rho-1 nonzero allows cancellation of the tail coefficient.

**Theorem 1.10 (Exact operator norm).**

$$\forall \rho\in \mathbb{C},\beta=\Re \rho> \frac{1}{2},\rho\neq1, \Vert J_{\rho}\Vert ^{2}=\frac{1}{2\beta-1}+\frac{1}{\Vert \rho-1\Vert ^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineFunctional_norm_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The isometry of the Riesz map identifies the operator norm with the kernel norm. The result is an equality, with both support contributions retained.

## References

- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineFunctional`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineFunctional_integral`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineFunctional_norm_sq`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineKernel`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineKernel_coe_ae`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.halflineKernel_norm_sq`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector_coe_ae`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector_nat`
- Truth anchor: `D5/S3/Observer/Hilbert/NymanHalflineMellinKernel.realSourceVector_tail`
- Dependency: [D5/S3/Observer/Hilbert/NymanBeurlingFiniteGramDistance](NymanBeurlingFiniteGramDistance.md)
