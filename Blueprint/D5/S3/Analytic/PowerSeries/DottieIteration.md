# Global convergence of the cosine iteration

## Abstract

The equation cos(t) = t has exactly one real solution theta, and the cosine iteration converges to theta from every real start, geometrically from the second iterate on, with ratio of consecutive errors tending to -sin(theta) along every orbit that avoids theta.

**Theorem 1.1 (The cosine iteration converges to its unique real fixed point).**

$$\exists \theta \in \mathbb{R}, 0 < \theta \land \left(\theta < 1 \land \left(\left(\forall t \in \mathbb{R},\; \operatorname{cos}\left(t\right) = t \Leftrightarrow t = \theta\right) \land \left(\forall x \in \mathbb{R},\; \operatorname{Tendsto}\left(n \mapsto \operatorname{cos}^{[n]}\left(x\right), \operatorname{atTop}, \operatorname{nhds}\left(\theta\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \left|\operatorname{cos}^{[n + 2]}\left(x\right) - \theta\right| \le \operatorname{sin}\left(1\right)^{n} \cdot \left(1 - \theta\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; \operatorname{cos}^{[n]}\left(x\right) \ne \theta\right) \Rightarrow \operatorname{Tendsto}\left(n \mapsto \frac{\operatorname{cos}^{[n + 1]}\left(x\right) - \theta}{\operatorname{cos}^{[n]}\left(x\right) - \theta}, \operatorname{atTop}, \operatorname{nhds}\left(-\operatorname{sin}\left(\theta\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PowerSeries/DottieIteration.cos_iterate_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All quantities are real and angles are in radians. In the formula cos^[n] denotes the n-fold composite of the cosine with itself, the zeroth composite being the identity, so cos^[n](x) is the n-th term of the orbit of the start x. The statement has four parts. There is a real number theta with 0 < theta < 1 such that a real t satisfies cos(t) = t exactly when t = theta. For every real start x the orbit cos^[n](x) tends to theta as n tends to infinity. From the second iterate on the error obeys the uniform bound |cos^[n+2](x) - theta| <= sin(1)^n (1 - theta) for every natural n, the same constant for all starts. If no term of the orbit equals theta, the ratio (cos^[n+1](x) - theta) / (cos^[n](x) - theta) of consecutive errors tends to -sin(theta).

Existence of theta in (0, 1) and its uniqueness among positive solutions are taken from the inverse-series endpoint theorem of the neighbouring document on the rational inverse series. Uniqueness among all real solutions follows because a solution t equals cos(t) and hence lies in [-1, 1], and the cosine is positive on [-1, 0], so no solution is less than or equal to zero.

The cosine maps [-1, 1] into [cos(1), 1], because it is even and decreasing on [0, 1]. Every first iterate lies in [-1, 1], so every second iterate lies in [cos(1), 1], and this interval is mapped into itself. For u and v in [0, 1] the identity cos(u) - cos(v) = -2 sin((u + v)/2) sin((u - v)/2), together with 0 <= sin((u + v)/2) <= sin(1) and |sin(s)| <= |s|, gives |cos(u) - cos(v)| <= sin(1) |u - v|. Applied along the orbit from the second iterate and to the fixed point theta, which also lies in [cos(1), 1], this gives |cos^[n+2](x) - theta| <= sin(1)^n |cos^[2](x) - theta|. Since cos(1) >= 1/2 and theta < 3/4, every point y of [cos(1), 1] satisfies |y - theta| <= 1 - theta, which yields the stated bound. Because 0 < sin(1) < 1, the bound tends to zero, and convergence of the orbit follows.

The constant 1 - theta cannot be decreased: for x = pi/2 one has cos(pi/2) = 0 and cos(0) = 1, so cos^[2](pi/2) = 1 and the bound holds with equality at n = 0. The ratio sin(1) is a uniform rate, not the asymptotic one. The derivative of the cosine at theta is -sin(theta), and since sin(theta)^2 = 1 - theta^2 and sin(theta) > 0, its absolute value is sqrt(1 - theta^2), which is smaller than sin(1). Writing the ratio of consecutive errors as the difference quotient (cos(y) - cos(theta)) / (y - theta) at y = cos^[n](x), and using cos(theta) = theta, the convergence of the orbit to theta through points different from theta turns the derivative into the limit of the ratios. Along such an orbit the errors therefore eventually alternate in sign.

The hypothesis that no term of the orbit equals theta cannot be removed from the last part. For the start x = -theta, evenness of the cosine gives cos(-theta) = theta, so every term from the first on equals theta. All later errors vanish; with the convention that division by zero gives zero, which the statement uses, the ratios are zero from n = 1 on and tend to 0, which differs from -sin(theta) because sin(theta) > 0. The same happens for every start of the form theta + 2 pi k or -theta + 2 pi k with an integer k.

Numerically theta = 0.7390851332..., sin(theta) = 0.6736120291... and sin(1) = 0.8414709848...; these decimals are not part of the statement. The statement concerns the real cosine only: the iteration of the complex cosine on the complex plane is not claimed. The number theta is transcendental by the Lindemann-Weierstrass theorem; transcendence is not part of the statement. The global convergence of the real cosine iteration is classical: it is a contraction argument of Banach fixed-point type, and the limit theta is widely known as the Dottie number.

## References

- Truth anchor: `D5/S3/Analytic/PowerSeries/DottieIteration.cos_iterate_tendsto`
- Dependency: [D5/S3/Analytic/PowerSeries/DottieInverseSeries](DottieInverseSeries.md)
