# Two-scale endpoint moments

## Abstract

Uniform moment concentration for signed two-scale exponential families, including coefficient cancellation.

**Theorem 1.1 (Every polynomial moment of a decreasing exponential).**

$$\forall r \in \mathbb {R},\; \left(0 < r\right) \Rightarrow \left(\forall k \in \mathbb {N},\; \operatorname {MeasureTheory.IntegrableOn}\left(t: \mathbb {R}\mapsto \left(t\right)^{k} \cdot \operatorname {Real.exp}\left(-\left(r \cdot t\right)\right), \operatorname {Set.Ioi}\left(0\right)\right) \land \operatorname {MeasureTheory.integral}\left(\operatorname {Measure.restrict}\left(\operatorname {volume}, \operatorname {Set.Ioi}\left(0\right)\right), t: \mathbb {R}\mapsto \left(t\right)^{k} \cdot \operatorname {Real.exp}\left(-\left(r \cdot t\right)\right)\right) = \frac{\operatorname {Nat.factorial}\left(k\right)}{\left(r\right)^{k + 1}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments.exponential_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real rate r and natural order k, the polynomially weighted exponential is integrable on the positive ray and its integral equals k! divided by r to the power k+1. The Gamma integral gives both assertions. The exact formula supplies the moments of each exponential term in the two-scale family.

**Theorem 1.2 (Uniform moments relative to the same source mass).**

Lean statement: `D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments.two_scale_endpoint_moment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments.two_scale_endpoint_moment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a, b, endpoint s, and p greater than zero, define F(x)=a exp(-p(x-s))+b exp(-2p(x-s)). For every natural k, the theorem proves integrability of (x-s)^k F(x)^2 on x>s, the coercive mass bound D at least (a^2+b^2)/(54p), and the uniform moment bound M_k at most 54 k! p^(-k) D. Here D and M_k are the actual Lebesgue integrals of this same F on x>s. Both coefficients may depend on p and may have opposite signs.

With t=p(x-s), the fixed shape is g(t)=a exp(-t)+b exp(-2t). Mathlib's real Gamma integral gives its exact k-th moment as k! times (a^2/2^(k+1)+2ab/3^(k+1)+b^2/4^(k+1)). Its mass is a^2/2+2ab/3+b^2/4. The identity 54D_shape-(a^2+b^2)=((26a+18b)^2+b^2)/26 controls cancellation. The positive moment upper bound is at most k!(a^2+b^2); translation invariance and positive dilation then give the stated estimate.

Nonzero coefficients therefore give positive mass. At a fixed positive endpoint, these bounds supply concentration of polynomially weighted mass as p tends to infinity. Applying the estimate to an actual Suzuki mean-zero source requires a separate proof of the source's trace condition and relevant domains; those conditions are not assumptions of this moment theorem.

## References

- Truth anchor: `D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments.exponential_moment`
- Truth anchor: `D5/S3/Analytic/ExponentialSum/TwoScaleEndpointMoments.two_scale_endpoint_moment_bound`
