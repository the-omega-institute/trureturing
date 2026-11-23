# The arithmetic bound at the actual cubic endpoint

## Abstract

The arithmetic bound at the actual cubic endpoint

**Theorem 1.1 (A lower bound for the normalized weighted Chebyshev error).**

$$\forall b \in \mathbb{R},\; \forall T \in \mathbb{R},\; \operatorname{log}\left(2\right) \le b \Rightarrow \left(0 < T \Rightarrow \left(\left(\forall k \in \mathbb{N},\; \left|\operatorname{Im}\left(\operatorname{rho}\left(k\right)\right)\right| \le T \Rightarrow \operatorname{Re}\left(\operatorname{rho}\left(k\right)\right) = \frac{1}{2}\right) \Rightarrow -\frac{\operatorname{W}\left(b\right)}{\operatorname{R}\left(b\right)} \cdot (\operatorname{exp}\left(\frac{-b}{2}\right) \cdot \operatorname{C3}\left(T\right) + \frac{\operatorname{C2}\left(T\right)}{T}) - \frac{\operatorname{log}\left(2 \cdot \pi\right) \cdot \operatorname{exp}\left(-b\right)}{b + 1} \le \operatorname{E}\left(\operatorname{exp}\left(b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicArithmetic.actual_cubic_arithmetic_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write E(x) for Q(x) minus the weighted tail of the Chebyshev error kernel at x divided by r(x). The occurrence rho(k) ranges over both ordinate signs and retains every analytic multiplicity. The masses C3(T) and C2(T) sum inverse cubes through T and inverse squares above T, respectively, with the cutoff on the absolute ordinate.

Logarithmic transport identifies R(b)E(exp(b)) with the integral of W(v)Q(exp(v)) over v > b, where W(v)=(v+2)/v^3 and R(v)=(v+1)/v^2. Use the exact signed explicit formula for Q(exp(v)). Its trivial-zero term contributes nonnegatively. The elementary weight W(v)exp(-v) has primitive -exp(-v)/v^2, which tends to zero, so the constant term integrates to -log(2*pi)exp(-b)/b^2.

The integrated spectral real part is bounded by the norm of the actual spectral tail. Apply the cubic endpoint estimate and divide by R(b)>0 to obtain the stated bound for each positive cutoff satisfying the critical-line premise.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicArithmetic.actual_cubic_arithmetic_lower_bound`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint](ActualCubicEndpoint.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualSignedGaussianEndpoint](ActualSignedGaussianEndpoint.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedTailTransport](../WeightedTailTransport.md)
