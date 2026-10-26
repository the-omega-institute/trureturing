# Relative Gaussian averaging of the clipped cosh kernel

## Abstract

The actual Gaussian-cosh local expansion remains a relative approximation after Gaussian averaging in both unbounded source-offset regimes.

Let phi be the existing standard normal density and J the existing Gaussian-cosh integral. All integrals below use Lebesgue measure. All fractional powers are real powers.

**Definition 1.1 (The exact local coefficient).**

$$\forall q \in \mathbb{R},\; A\left(q\right)=\frac{4\sqrt{2}\varphi(0)}{3\cdot q}$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.coshCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This coefficient uses the value at zero of the standard normal density.

**Definition 1.2 (The shifted affine displacement).**

$$\forall b \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall v \in \mathbb{R},\; d\left(b, t, v\right)=b\cdot {(v-t)}-\frac{b^{2}}{2}$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.affineOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quadratic shift is part of the displacement at every parameter value.

**Definition 1.3 (The actual three-halves moment).**

$$\forall b \in \mathbb{R},\; \forall t \in \mathbb{R},\; K\left(b, t\right)=\int_{\mathbb{R}} \varphi(v)\cdot \max{\{d\left(b, t, v\right),0\}}^{\frac{3}{2}} dv$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.positiveMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive part is taken before the fractional power and Gaussian integration.

**Definition 1.4 (The actual averaged kernel).**

$$\forall q \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall t \in \mathbb{R},\; N\left(q, b, t\right)=\int_{\mathbb{R}} \varphi(v)\cdot J\left(q, d\left(b, t, v\right)\right) dv$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.averagedCosh` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inner kernel is the actual Gaussian-cosh integral, evaluated at the shifted displacement.

**Definition 1.5 (The nonlocal exponential envelope).**

$$\forall b \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall e \in \mathbb{R},\; T\left(b, t, e\right)=\int_{\{v\in \mathbb{R}\mid e< d\left(b, t, v\right)\}} \varphi(v)\cdot exp\left(d\left(b, t, v\right)\right) dv$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.nonlocalEnvelope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integration set is the strict superlevel set of the actual displacement.

**Definition 1.6 (The source normalized offset).**

$$\forall q \in \mathbb{R},\; \forall b \in \mathbb{R},\; tau\left(q, b\right)=\frac{log\left(4\right)-\frac{q^{2}}{2}}{b}$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.sourceOffset` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalized offset uses the same positive parameters as the source sequence.

The integrability clauses use the following three actual functions, with every argument displayed:

$\forall q \in \mathbb{R},\; \forall e \in \mathbb{R},\; \forall u \in \mathbb{R},\; inner\left(q, e, u\right)=\varphi(u)\cdot \max{\{exp\left(e\right)-cosh\left(q\cdot u\right),0\}}$

$\forall q \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall v \in \mathbb{R},\; outer\left(q, b, t, v\right)=\varphi(v)\cdot J\left(q, d\left(b, t, v\right)\right)$

$\forall b \in \mathbb{R},\; \forall t \in \mathbb{R},\; \forall v \in \mathbb{R},\; moment\left(b, t, v\right)=\varphi(v)\cdot \max{\{d\left(b, t, v\right),0\}}^{\frac{3}{2}}$

**Theorem 1.7 (The relative limit in both unbounded regimes).**

$$\forall q \in (\mathbb{N}\to \mathbb{R}),\; \forall b \in (\mathbb{N}\to \mathbb{R}),\; {({(\forall n \in \mathbb{N},\; 0< q\left(n\right))}\land {(\forall n \in \mathbb{N},\; 0< b\left(n\right))}\land \lim_{n\to \infty} q\left(n\right)=\sqrt{2\cdot log\left(4\right)}\land \lim_{n\to \infty} b\left(n\right)=0\land {(\lim_{n\to \infty} tau\left(q\left(n\right), b\left(n\right)\right)=\infty\lor \lim_{n\to \infty} tau\left(q\left(n\right), b\left(n\right)\right)=-\infty)})}\Rightarrow {({(\forall n \in \mathbb{N},\; {({(\forall v \in \mathbb{R},\; Integrable\left(inner\left(q\left(n\right), d\left(b\left(n\right), tau\left(q\left(n\right), b\left(n\right)\right), v\right)\right)\right))}\land Integrable\left(outer\left(q\left(n\right), b\left(n\right), tau\left(q\left(n\right), b\left(n\right)\right)\right)\right)\land Integrable\left(moment\left(b\left(n\right), tau\left(q\left(n\right), b\left(n\right)\right)\right)\right)\land 0< K\left(b\left(n\right), tau\left(q\left(n\right), b\left(n\right)\right)\right)\land 0< A\left(q\left(n\right)\right)\land 0< A\left(q\left(n\right)\right)\cdot K\left(b\left(n\right), tau\left(q\left(n\right), b\left(n\right)\right)\right))})}\land \lim_{n\to \infty} \frac{N\left(q\left(n\right), b\left(n\right), tau\left(q\left(n\right), b\left(n\right)\right)\right)}{A\left(q\left(n\right)\right)\cdot K\left(b\left(n\right), tau\left(q\left(n\right), b\left(n\right)\right)\right)}=1)}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.gaussian_cosh_source_relative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Q=sqrt(2 log(4)), q(n) and b(n) are positive at every natural index, and t(n)=tau(q(n),b(n)). The formula includes integrability of each inner kernel, the outer kernel and the moment integrand at every index, together with strict positivity of K, A and their product. No asymptotic integral or tail estimate is a hypothesis.

The nonlocal envelope satisfies T(b(n),t(n),e)/K(b(n),t(n)) tending to zero for every fixed positive e. On the positive side, the change of variables v=t+z/t extracts the common factor phi(t)(b/t)^(3/2)/t. The remaining moment integral tends to the strictly positive integral of z^(3/2) exp(-z) over positive z. The shift is exactly b t/2. The normalized tail is dominated by the cutoff to the power -3/2 times z^(3/2) exp(-z/2) and vanishes pointwise. Thus the exponentially small density factor cancels before taking the ratio.

On the negative side write t=-L. Division by (bL)^(3/2) leaves the positive part of 1+v/L-b/(2L), raised to the three-halves power. Its Gaussian integral tends to one. The normalized nonlocal envelope is dominated by a constant times phi(v)(1+v^2) exp(1+abs(v)), an integrable function. It also vanishes pointwise.

Split the error at displacement e. The local remainder is at most C e K. On the nonlocal set, J(d) is at most exp(d) and d^(3/2) is at most 4 exp(d), so the integrated error is at most C e K+(1+4A)T. Divide by the positive A K, use the proved relative tail limit, and let e decrease to zero. The source relation b t=log(4)-q^2/2 supplies b t tending to zero.

This establishes the analytic averaging formula of equation 14.16. No Bayes identity, moment comparison, full crossover theorem or additional offset regime is asserted.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.affineOffset`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.averagedCosh`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.coshCoefficient`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.gaussian_cosh_source_relative`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.nonlocalEnvelope`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.positiveMoment`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshAveraging.sourceOffset`
- Dependency: [D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel](GaussianCoshKernel.md)
