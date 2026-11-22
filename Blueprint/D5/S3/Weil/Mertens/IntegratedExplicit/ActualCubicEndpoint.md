# Cubic resolvent bounds at the actual spectral endpoint

## Abstract

Cubic resolvent bounds at the actual spectral endpoint

**Theorem 1.1 (A single resolvent mode).**

$$\forall z \in \mathbb{C},\; \operatorname{Re}\left(z\right) \le 1 \Rightarrow \left(1 - z \ne 0 \Rightarrow \left(\forall b \in \mathbb{R},\; 0 < b \Rightarrow \left\lVert \operatorname{mode}\left(z, b\right) \right\rVert \le \frac{\operatorname{W}\left(b\right) \cdot \operatorname{exp}\left((\operatorname{Re}\left(z\right) - 1) \cdot b\right)}{\left\lVert 1 - z \right\rVert}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint.resolventMode_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nonnegative Laplace variable s, the norm of s+1-z is at least the norm of 1-z when Re(z) <= 1. The exponential norm factors into the decay at the endpoint b and exp(-s*b). Integrating the remaining Laplace polynomial gives the original weight W(b)=(b+2)/b^3.

**Theorem 1.2 (The finite-height split).**

$$\forall b \in \mathbb{R},\; \forall T \in \mathbb{R},\; 0 < b \Rightarrow \left(0 < T \Rightarrow \left(\left(\forall k \in \mathbb{N},\; k \in \operatorname{L}\left(T\right) \Rightarrow \operatorname{Re}\left(\operatorname{rho}\left(k\right)\right) = \frac{1}{2}\right) \Rightarrow \left(\operatorname{Finite}\left(\operatorname{L}\left(T\right)\right) \land \left(\left\lVert \operatorname{spectralTail}\left(S, b\right) \right\rVert \le \operatorname{W}\left(b\right) \cdot (\operatorname{exp}\left(\frac{-b}{2}\right) \cdot \operatorname{C3}\left(T\right) + \frac{\operatorname{C2}\left(T\right)}{T}) \land \operatorname{C2}\left(T\right) \le \frac{101}{100} \cdot M\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint.actual_spectral_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write rho(k) for the actual zero at occurrence k. The set L(T) contains every k with abs(Im(rho(k))) <= T. Both ordinate signs and all analytic multiplicities are included. The mass C3(T) sums inverse cubes of the absolute ordinate over L(T). The mass C2(T) sums inverse squares over its complement. S is the complete actual spectrum and M is the existing first Li mass.

The coefficient contributes one denominator from rho(k) and one from 1-rho(k). The mode contributes another denominator from 1-rho(k). Each denominator is bounded below by the absolute ordinate. Reciprocal-square summability proves L(T) finite and permits the countable resolvent sum to split at T. The critical-line premise gives exp(-b/2) on L(T). Above T, strip membership bounds the exponential by one, and the third inverse ordinate is bounded by 1/T.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint.actual_spectral_tail_bound`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualCubicEndpoint.resolventMode_norm_le`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualSignedGaussianEndpoint](ActualSignedGaussianEndpoint.md)
