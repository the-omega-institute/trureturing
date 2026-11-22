# Fourier recovery at every positive logarithmic width

## Abstract

A width-uniform error estimate at each tested frequency

**Theorem 1.1 (The error constant can be chosen before the width).**

$$\mathit{RH} \Rightarrow \left(\exists B \in \mathbb{R},\; 0 < B \land \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\left(\forall w \in \mathbb{R},\; \exists C \in \mathbb{R},\; 0 < C \land \left(\forall L \in \mathbb{R},\; 0 < L \Rightarrow \left(\forall U \in \mathbb{R},\; \forall T \in \mathbb{R},\; \left(B \le U \land 0 < T\right) \Rightarrow \left(\operatorname{Integrable}\left(m, L, w, U, T\right) \land \left\lVert \operatorname{Avg}\left(m, L, w, U, T\right) - \operatorname{A}\left(m, r, L, w\right) \right\rVert \le \frac{C}{T}\right)\right)\right)\right) \land \left(\forall L \in \mathbb{R},\; 0 < L \Rightarrow \left(\operatorname{A}\left(m, r, L, 0\right) = -\operatorname{c}\left(m\right) \land \left(\forall z \in \mathbb{C},\; \operatorname{Nontrivial}\left(z\right) \Rightarrow \left(\operatorname{A}\left(m, r, L, \operatorname{omega}\left(z, r\right)\right) = -\operatorname{mu}\left(r\right) \cdot \operatorname{Mult}\left(z\right) \cdot \operatorname{W}\left(r, L, z\right) \land \operatorname{W}\left(r, L, z\right) \ne 0\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffUniformWidth.signed_window_even_cutoff_fourier_uniform_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use q=m+1=2r, s=1/2−1/q and c(m)=μ(q)q/(m s). The original signed residual at exp(u), exp(u+L) is divided by their power gap and multiplied by exp(−iwu). Avg is its interval mean over [U,U+T], and Integrable asserts Lebesgue integrability on that interval.

Let ω(ρ,r)=Im(ρ)/r. The contribution W(r,L,ρ) is 2r²/[ρ(r−ρ)(r−2ρ)] times (exp((−s+iω(ρ,r))L)−1)/(1−exp(−sL)). A(m,r,L,w) is −μ(r) times the sum over all occurrences with ω(ρ,r)=w, with −c(m) added at w=0. Mult is the analytic order of the zero.

The width multiplier has modulus at most 1+|ω(ρ,r)|/s for every L>0. Split its numerator at exp(−sL) and use the bound on the complex phase increment together with L exp(−sL)/(1−exp(−sL))≤1/s. The modulus of the root exponent absorbs the extra frequency factor. The resulting coefficient majorant is summable and independent of L. The Fourier error is bounded by a term independent of L plus a multiple of the norm sum, all divided by T.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffUniformWidth.signed_window_even_cutoff_fourier_uniform_width`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourier](RHMobiusEvenCutoffFourier.md)
