# Recovering zeta zero frequencies and multiplicities

## Abstract

Fourier coefficients of the even-cutoff signed prime window

**Theorem 1.1 (Quantitative coefficient recovery).**

$$\mathit{RH} \Rightarrow \left(\exists B \in \mathbb{R},\; 0 < B \land \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\forall L \in \mathbb{R},\; 0 < L \Rightarrow \left(\left(\forall w \in \mathbb{R},\; \exists C \in \mathbb{R},\; 0 < C \land \left(\forall U \in \mathbb{R},\; \forall T \in \mathbb{R},\; \left(B \le U \land 0 < T\right) \Rightarrow \left(\operatorname{Integrable}\left(m, L, w, U, T\right) \land \left\lVert \operatorname{Avg}\left(m, L, w, U, T\right) - \operatorname{A}\left(m, r, L, w\right) \right\rVert \le \frac{C}{T}\right)\right)\right) \land \left(\operatorname{A}\left(m, r, L, 0\right) = -\operatorname{c}\left(m\right) \land \left(\forall z \in \mathbb{C},\; \operatorname{Nontrivial}\left(z\right) \Rightarrow \left(\operatorname{A}\left(m, r, L, \operatorname{omega}\left(z, r\right)\right) = -\operatorname{mu}\left(r\right) \cdot \operatorname{Mult}\left(z\right) \cdot \operatorname{W}\left(r, L, z\right) \land \operatorname{W}\left(r, L, z\right) \ne 0\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourier.signed_window_even_cutoff_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write q=m+1=2r and s=1/2−1/q. Let c(m)=μ(q)q/(m s), and let ω(ρ,r)=Im(ρ)/r. The function with integral Avg(m,L,w,U,T) times T is the original signed residual at endpoints exp(u), exp(u+L), divided by their power gap and multiplied by exp(−iwu). Integrable denotes Lebesgue interval integrability on [U,U+T].

The factor W(r,L,ρ) is 2r² divided by ρ(r−ρ)(r−2ρ), multiplied by (exp((−s+iω(ρ,r))L)−1)/(1−exp(−sL)). The target A(m,r,L,w) is the sum of these factors over actual zero occurrences with ω(ρ,r)=w, scaled by −μ(r). At w=0 add the arithmetic constant −c(m). Nontrivial(ρ) means a nontrivial zeta zero and Mult(ρ) is its analytic order of vanishing.

Conjugation of the actual zero occurrences makes the normalized root series real. After multiplication by exp(−iwu), all frequencies outside the matching fiber have positive separation from zero. Local finiteness of the distinct zeros gives this separation in a bounded region. Termwise integration of the absolutely summable series bounds the contribution outside the fiber independently of U and T. The normalized arithmetic remainder has an integrable exponential bound. At an actual zero, the whole fiber consists of exactly its analytic number of occurrences. The modulus of the exponential in the numerator of the width factor is exp(−sL)<1.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourier.signed_window_even_cutoff_fourier`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff](RHMobiusEvenCutoff.md)
