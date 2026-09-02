# Euler-Boundary Exact Dispersion

## Abstract

Euler-boundary log-cosh dispersion realizes the exact hyperbolic rapidity identities.

**Definition 1.1 (Limiting speed scale).**

$$c_{\infty}:=\frac{\pi}{2}$$

*Formalization.* `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.cInfinity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source normalization fixes the limiting speed scale at pi over two.

**Definition 1.2 (Rapidity coordinate).**

$$\forall k\in\mathbb{R},\ \theta(k):=c_{\infty}k$$

*Formalization.* `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.rapidity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rapidity is the limiting speed scale multiplied by the wave number.

**Definition 1.3 (Euler-boundary energy).**

$$\forall k\in\mathbb{R},\ E_{1}(k):=\log \operatorname{cosh}(\theta(k))$$

*Formalization.* `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.eulerBoundaryEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The dispersion is the logarithm of the hyperbolic cosine of rapidity.

**Definition 1.4 (Euler-boundary group velocity).**

$$\forall k\in\mathbb{R},\ v_{1}(k):=\frac{dE_{1}}{dk}(k)$$

*Formalization.* `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.eulerBoundaryVelocity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Group velocity is the ordinary real derivative of the dispersion.

**Theorem 1.5 (Euler-boundary exact dispersion).**

$$\begin{aligned}\forall k\in\mathbb{R},\ E_{1}(k) = \log \operatorname{cosh}(\frac{\pi k}{2}) \land\\v_{1}(k) = \frac{\pi}{2}\operatorname{tanh}(\frac{\pi k}{2}) \land\\e^{E_{1}(k)} = \operatorname{cosh}(\theta(k)) \land\\\frac{v_{1}(k)}{c_{\infty}} = \operatorname{tanh}(\theta(k)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.euler_boundary_exact_dispersion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real wave number, the derivative witness computes the group velocity as c-infinity times tanh of rapidity. Positivity of cosh justifies exponentiating the logarithm, and positivity of pi keeps the normalized velocity away from totalized division by zero.

## References

- Truth anchor: `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.cInfinity`
- Truth anchor: `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.eulerBoundaryEnergy`
- Truth anchor: `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.eulerBoundaryVelocity`
- Truth anchor: `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.euler_boundary_exact_dispersion`
- Truth anchor: `D5/S3/CompletionDynamics/EulerBoundaryExactDispersion.rapidity`
