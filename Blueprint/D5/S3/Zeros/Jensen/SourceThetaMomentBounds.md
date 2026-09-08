# Literal Theta Moment Bounds

## Abstract

Literal theta moments are positive and finite under a summable Gaussian bound.

Phi is sourceThetaKernel, the fixed even theta series. The symbols a(k) and p(x) denote sourceThetaCoefficient(k) and sourceThetaDensity(x). Z is the real part of xiReading(1/2), and p(x)=Phi(x)/Z. No central-value integral identity is assumed in the analytic estimates.

**Definition 1.1 (Literal summand).**

$$\forall n\in \mathbb{N},x\in \mathbb{R}:T_{n}(x)=(4\pi^{2}(n+1)^{4}\exp(\frac{9|x|}{2})-6\pi(n+1)^{2}\exp(\frac{5|x|}{2}))\exp(-\pi(n+1)^{2}\exp(2|x|))$$

*Formalization.* `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.thetaSummand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index n starts at zero, so n+1 runs over the positive integers. This is exactly the summand of the fixed kernel.

**Definition 1.2 (Gaussian coefficients).**

$$\forall n\in \mathbb{N}:b_{n}=4\pi^{2}(n+1)^{4}\exp(\frac{-\pi(n+1)^{2}}{2})$$

*Formalization.* `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.thetaMajorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These positive real coefficients give a bound independent of x.

**Theorem 1.3 (Positive summand estimate).**

$$\forall n\in \mathbb{N},x\in \mathbb{R}:0< T_{n}(x)\land T_{n}(x)\le b_{n}\exp(-x^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_summand_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t=|x| and m=n+1, factor the difference using exp(9t/2)=exp(5t/2)exp(2t). Positivity follows from pi>3 and m>=1. For the upper bound, drop the negative term and use m^2 exp(2t)>=(m^2+exp(2t))/2 and exp(2t)>=1+2t+2t^2. The remaining quadratic is 2(t-3/8)^2+39/32, which is positive.

**Theorem 1.4 (Summable majorant).**

$$\operatorname{Summable}(n\mapsto b_{n})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_majorant_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summability is over n in the natural numbers. Compare b(n) with 4 pi^2 (n+1)^4 exp(-pi(n+1)/2), a shifted polynomial times a geometric sequence.

**Theorem 1.5 (Pointwise convergence).**

$$\forall x\in \mathbb{R}:\operatorname{Summable}(n\mapsto T_{n}(x))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed real x, the entire natural-indexed summand sequence is summable by the positive majorant. This verifies convergence of the literal tsum.

**Theorem 1.6 (Continuity).**

$$\phi\in C^{0}(\mathbb{R},\mathbb{R})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every summand is continuous. Since exp(-x^2)<=1, the summable b(n) bound is uniform on the whole real line; uniform summability gives continuity.

**Theorem 1.7 (Evenness).**

$$\forall x\in \mathbb{R}:\phi(-x)=\phi(x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Absolute value is unchanged by negation, so every literal summand and the sum are even.

**Theorem 1.8 (Positive Gaussian bound).**

$$\forall x\in \mathbb{R}:0< \phi(x)\land \phi(x)\le (\sum_{n=0}^{\infty}b_{n})\exp(-x^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_gaussian_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One strictly positive summand gives positivity of Phi. Summing the estimates gives the displayed bound with the finite explicit constant sum b(n). At x=0 the same inequality also shows that this constant is strictly positive.

**Theorem 1.9 (All raw even moments).**

$$\forall k\in \mathbb{N}:(x\mapsto x^{2k}\phi(x))\in L^{1}(\mathbb{R})\land 0< \int_{\mathbb{R}}x^{2k}\phi(x)\,dx$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_raw_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Integrability is with respect to real Lebesgue measure. Polynomial-Gaussian integrability and the kernel bound dominate each even moment. The integrand is continuous and nonnegative and is strictly positive at x=1, so its integral is positive.

**Theorem 1.10 (Normalization from the constant coefficient).**

$$a_{0}=1\implies Z=\int_{\mathbb{R}}\phi(x)\,dx\land 0< Z\land \int_{\mathbb{R}}p(x)\,dx=1\land (\forall k\in \mathbb{N}:0< a_{k})$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here Z=Re(xiReading(1/2)) and a(k) is the actual density moment divided by (2k)!. The unit constant coefficient first excludes Z=0. Pulling the constant denominator through the integral yields Z equal to the positive raw mass. All raw even moments and factorial denominators are positive. This result is conditional on a(0)=1; it does not independently establish a xi/theta integral identity.

## References

- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_continuous`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_even`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_gaussian_bound`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_majorant_summable`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_normalization`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_raw_moments`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_summable`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.source_theta_summand_bounds`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.thetaMajorant`
- Truth anchor: `D5/S3/Zeros/Jensen/SourceThetaMomentBounds.thetaSummand`
- Dependency: [D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering](NormalizedJensenDegreeLowering.md)
