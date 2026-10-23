# Factorial Taylor error for bounded observations

## Abstract

Factorial Taylor error for bounded observations

**Theorem 1.1 (Pointwise Taylor error).**

$$\forall K, V, W, [RCLike\left(K\right)] [Banach\left(K, V\right)] [Nonzero\left(V\right)] [NormedSpace\left(K, W\right)], \forall B: BoundedLinearMap\left(K, V, V\right), \forall C: BoundedLinearMap\left(K, V, W\right), \forall N\in \mathbb{N}, \forall t\ge 0, \forall x\in V, \left\lVert C\left(\exp(tB)\left(x\right)\right)-p\left(B, C, N, t, x\right) \right\rVert\le \frac{\left\lVert C \right\rVert\exp(b\left(B\right)t)(b\left(B\right)t)^{N+1}}{(N+1)!}\left\lVert x \right\rVert$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ExactTaylorObservationRemainder.norm_observation_taylor_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a nonzero complete normed space and W a normed space over the real or complex field. Let B:V→V and C:V→W be bounded linear maps, N a natural number, t≥0 and x∈V. No dimension restriction is imposed.

Write b(B)=max(1,‖B‖), c(C)=‖C‖, and p(B,C,N,t,x)=the sum of t^k C(B^k x)/k! for 0≤k≤N. The exponential is the norm-convergent Banach algebra exponential.

The factorial convolution inequality n! k!≤(n+k)! bounds the exponential series tail by r^n exp(r)/n! whenever ‖z‖≤r. Applying C and evaluating at x gives the displayed estimate without a radius restriction.

**Theorem 1.2 (Integrated squared Taylor error).**

$$\forall K, V, W, [RCLike\left(K\right)] [Banach\left(K, V\right)] [Nonzero\left(V\right)] [NormedSpace\left(K, W\right)], \forall B: BoundedLinearMap\left(K, V, V\right), \forall C: BoundedLinearMap\left(K, V, W\right), \forall N\in \mathbb{N}, \forall T\ge 0, \forall x\in V, \int_{0}^{T}\left\lVert C\left(\exp(tB)\left(x\right)\right)-p\left(B, C, N, t, x\right) \right\rVert^{2} dt\le (\frac{\left\lVert C \right\rVert\exp(b\left(B\right)T)b\left(B\right)^{N+1}}{(N+1)!})^{2}\frac{T^{2N+3}}{2N+3}\left\lVert x \right\rVert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/ExactTaylorObservationRemainder.observation_taylor_energy_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, let T≥0. The squared norm is integrated with respect to ordinary Lebesgue measure on [0,T]. The result also holds at T=0.

On this interval exp(bt)≤exp(bT). Squaring the pointwise estimate and integrating t^(2N+2) gives exactly the denominator 2N+3. Completeness is needed only for the state-space exponential, not for the scalar energy integral.

## References

- Truth anchor: `D5/S3/Observer/Linear/ExactTaylorObservationRemainder.norm_observation_taylor_remainder`
- Truth anchor: `D5/S3/Observer/Linear/ExactTaylorObservationRemainder.observation_taylor_energy_remainder`
