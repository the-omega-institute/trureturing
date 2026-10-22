# A uniform Gaussian-cosh local kernel

## Abstract

The Gaussian positive-part cosh integral has a uniform local expansion on every positive compact interval.

Write phi for the existing standard normal density, with the exact normalization$\forall u \in \mathbb{R},\; \varphi(u)=\frac{exp\left(-\frac{u^{2}}{2}\right)}{\sqrt{2\pi}}$

Use the following kernel, with the positive part taken before integration:$\forall q \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall u \in \mathbb{R},\; K\left(q, d, u\right)=\varphi(u)\cdot \max{\{exp\left(d\right)-cosh\left(q\cdot u\right),0\}}$

**Definition 1.1 (The actual clipped Gaussian integral).**

$$\forall q \in \mathbb{R},\; \forall d \in \mathbb{R},\; J\left(q, d\right)=\int_{\mathbb{R}} K\left(q, d, u\right) du$$

*Formalization.* `D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel.gaussianCoshIntegral` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integral uses Lebesgue measure on the whole real line. Its integrand is bounded by exp(d) times the standard normal density, so it is integrable for every real q and d.

**Theorem 1.2 (The exact coefficient and a uniform fifth-half-power remainder).**

$$\forall lo \in \mathbb{R},\; \forall hi \in \mathbb{R},\; 0< lo\Rightarrow \exists delta \in \mathbb{R},\; \exists C \in \mathbb{R},\; 0< delta\land 0\le C\land \forall q \in \mathbb{R},\; q\in [lo,hi]\Rightarrow \forall d \in \mathbb{R},\; 0< d\land d\le delta\Rightarrow Integrable\left(K\left(q, d\right)\right)\land \left|J\left(q, d\right)-\frac{4\sqrt{2}\varphi(0)}{3\cdot q}\cdot d^{\frac{3}{2}}\right|\le C\cdot d^{\frac{5}{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel.gaussian_cosh_uniform_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed positive lower endpoint, one choice is delta=1/4 and C=4 phi(0)(5+2/lo^2)/lo. The same constants work for every q in the closed interval, including a singleton interval. The theorem also allows an upper endpoint below the lower endpoint, in which case the interval is empty.

Compare the clipped kernel with phi(0) times the positive part of d-(qu)^2/2. For d at most 1/4, both vanish outside the interval |u| at most 2 sqrt(d)/q. The cosh series gives cosh(x) at least 1+x^2/2. The upper bound cosh(x) at most exp(x^2/2), combined with the quadratic exponential remainder, bounds the clipped-kernel discrepancy by 5d^2.

The density changes by at most phi(0)u^2/2 from its value at zero. On the common interval, u^2 is at most 4d/lo^2. Thus the weighted integrand error is at most phi(0)(5+2/lo^2)d^2. Its integration interval has length 4 sqrt(d)/q. The exact integral of the leading clipped parabola is 4 sqrt(2)d^(3/2)/(3q), giving the stated coefficient and remainder.

This is the local-kernel estimate in equation 14.5 of the categorical decision blindness theory, strengthened to arbitrary positive compact intervals. It does not assert a Bayes-risk identity or either complete crossover theorem. The powers are real powers and d is strictly positive.

## References

- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel.gaussianCoshIntegral`
- Truth anchor: `D5/S3/TotalVariation/Asymptotics/GaussianCoshKernel.gaussian_cosh_uniform_remainder`
- Dependency: [D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers](StatLeanFourierSuppliers.md)
- Dependency: [D5/S3/Zeros/Jensen/FactorialJensenKernelBound](../../Zeros/Jensen/FactorialJensenKernelBound.md)
