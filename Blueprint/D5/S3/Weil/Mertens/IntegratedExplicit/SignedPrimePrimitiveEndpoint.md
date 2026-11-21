# One-sided constant bounds from 5040

## Abstract

The exact exponential endpoint for the signed prime primitive

**Theorem 1.1 (Either sign at the exact rate characterizes the strip above one half).**

$$\forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; \left(\frac{1}{2} < b \land c \ne 0\right) \Rightarrow \left(\left(\forall r \in \mathbb{C},\; \zeta(r) = 0 \Rightarrow \operatorname{Re}\left(r\right) \le b\right) \Leftrightarrow \left(\exists B \in \mathbb{R},\; 0 \le B \land \left(\exists Y \in \mathbb{R},\; \forall T \in \mathbb{R},\; Y \le T \Rightarrow c \cdot \int_{5040}^{\operatorname{exp}\left(T\right)}\frac{\operatorname{Qtheta}\left(x\right)}{\sqrt{x}}\,dx \le \operatorname{exp}\left((b - \frac{1}{2}) \cdot T\right) \cdot B\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveEndpoint.zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write Qθ(x) for the integral of (θ(u)−u)/u² over u>x. The signed primitive integrates Qθ(x)/√x from 5040 to exp(T). Each nonzero real c specifies one one-sided test.

If all zero real parts are at most b, the absolute tail estimate in PrimeAttainedCriticalWidth bounds |x^(1−b) Qθ(x)| by a constant C for all sufficiently large x. With x=exp(t), the logarithmic density is exp(t/2) Qθ(exp(t)). Multiplying the normalized bound by exp((b−1/2)t) therefore bounds the density in absolute value by C exp((b−1/2)t). Integrating the exponential bound and absorbing the finite initial interval from log(5040) gives the constant majorant for either sign.

The one-sided affine continuation criterion applies with zero linear coefficient when b<1. For b≥1, the zeta zero-free half-plane gives the asserted strip directly.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveEndpoint.zeta_strip_iff_signedPrimePrimitive_constant_bound_from_5040`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeAttainedCriticalWidth](PrimeAttainedCriticalWidth.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion](SignedPrimePrimitiveCriterion.md)
