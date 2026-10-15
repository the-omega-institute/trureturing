# An explicit observation floor on every positive window

## Abstract

An explicit observation floor on every positive window

**Theorem 1.1 (Finite derivative coercivity forces every positive window).**

$$\forall K, V, W, [RCLike\left(K\right)] [HilbertSpace\left(K, V\right)] [Nonzero\left(V\right)] [InnerProductSpace\left(K, W\right)], \forall B: BoundedLinearMap\left(K, V, V\right), \forall C: BoundedLinearMap\left(K, V, W\right), \forall N\in \mathbb{N}, \forall \mu, T\in \mathbb{R}, 0< \mu \land \mu\le mu\left(B, C, N\right) \land 0< T\Rightarrow\\{}0< r\left(B, C, N\right) \land 0< \tau\left(B, C, N, \mu\right) \land \alpha\left(N, \mu\right)\min\left(T, \tau\left(B, C, N, \mu\right)\right)^{2N+1}\le a\left(B, C, T\right) \land 0< \alpha\left(N, \mu\right)\min\left(T, \tau\left(B, C, N, \mu\right)\right)^{2N+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/PositiveWindowObservationBound.positive_window_observation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be the real or complex field, V a nonzero Hilbert space over K, W an inner-product space over K, and B:V→V and C:V→W bounded linear maps. Both spaces may be infinite dimensional; W need not be complete.

Define a(B,C,T) as the infimum over ‖x‖=1 of the actual integral from 0 to T of ‖C exp(tB)x‖^2. Define mu(B,C,N) as the infimum on the same unit sphere of the sum of ‖C B^k x‖^2 for 0≤k≤N. These are genuine real infima; neither is assumed attained.

For N≥0, H(N) has entries 1/(i+j+1), 0≤i,j≤N, and lambda(N) is its least eigenvalue. Put b=max(1,‖B‖), c=‖C‖, d(N,mu)=sqrt(lambda(N) mu)/N!, r(B,C,N)=c exp(b) b^(N+1)/((N+1)! sqrt(2N+3)), tau(B,C,N,mu)=min(1,d(N,mu)/(2r(B,C,N))), and alpha(N,mu)=lambda(N) mu/(4(N!)^2).

Suppose mu>0 and mu≤mu(B,C,N). The derivative inequality forces C to be nonzero, so r is strictly positive and the cutoff is defined with a positive denominator. The displayed conclusions hold for every T>0, including N=0 and equality at the cutoff.

For a unit state, the degree-N Taylor polynomial has energy at least d^2 T^(2N+1) when T≤1. The remainder has energy at most r^2 T^(2N+3). At T≤tau this is at most one quarter of the polynomial floor.

For an infinite-dimensional example with a necessary first derivative, take V=ℓ²(N,R)⊕₂ℓ²(N,R), W=ℓ²(N,R), B(u,v)=(v,0), and C(u,v)=u. Here B²=0, the zeroth derivative floor is zero, and the first derivative energy is ‖u‖²+‖v‖², so its unit-sphere floor is at least one. Taking N=1 and mu=1 gives a positive cubic short-window lower bound despite the nontrivial kernel of C.

The squared norm inequality ‖p‖^2≤2‖f‖^2+2‖f-p‖^2 then gives one quarter of the leading energy for f(t)=C exp(tB)x. Nonnegative integral monotonicity extends the bound from min(T,tau) to T. Taking the unit-sphere infimum proves the uniform estimate without compactness, separability, spectral stability, or an eigenvector of the observation operator.

## References

- Truth anchor: `D5/S3/Observer/Linear/PositiveWindowObservationBound.positive_window_observation_bound`
- Dependency: [D5/S3/Observer/Linear/ExactTaylorObservationRemainder](ExactTaylorObservationRemainder.md)
- Dependency: [D5/S3/Observer/Linear/HilbertMomentCoercivity](HilbertMomentCoercivity.md)
