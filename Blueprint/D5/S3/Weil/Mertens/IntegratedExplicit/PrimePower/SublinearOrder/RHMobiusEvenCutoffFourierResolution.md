# Finite averaging resolution of the signed prime window

## Abstract

Frequency offsets of order one over the averaging length

**Theorem 1.1 (The unit interval Fourier profile).**

$$\mathit{RH} \Rightarrow \left(\exists B \in \mathbb{R},\; 0 < B \land \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\left(\forall w \in \mathbb{R},\; \exists C \in \mathbb{R},\; 0 < C \land \left(\forall L \in \mathbb{R},\; 0 < L \Rightarrow \left(\forall U \in \mathbb{R},\; \forall T \in \mathbb{R},\; \left(B \le U \land 0 < T\right) \Rightarrow \left(\forall R \in \mathbb{R},\; \forall v \in \mathbb{R},\; \left(0 \le R \land \left|v\right| \le R\right) \Rightarrow \left(\operatorname{Integrable}\left(m, L, w, U, T, v\right) \land \left\lVert \operatorname{Avg}\left(m, L, w, U, T, v\right) - \operatorname{A}\left(m, r, L, w\right) \cdot \operatorname{K}\left(v\right) \right\rVert \le \frac{C \cdot \left(1 + R\right)}{T}\right)\right)\right)\right)\right) \land \left(\forall L \in \mathbb{R},\; 0 < L \Rightarrow \left(\operatorname{A}\left(m, r, L, 0\right) = -\operatorname{c}\left(m\right) \land \left(\forall z \in \mathbb{C},\; \operatorname{Nontrivial}\left(z\right) \Rightarrow \left(\operatorname{A}\left(m, r, L, \operatorname{omega}\left(z, r\right)\right) = -\operatorname{mu}\left(r\right) \cdot \operatorname{Mult}\left(z\right) \cdot \operatorname{W}\left(r, L, z\right) \land \operatorname{W}\left(r, L, z\right) \ne 0\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourierResolution.signed_window_even_cutoff_detuned_fourier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use q=m+1=2r, s=1/2−1/q and c(m)=μ(q)q/(m s). Divide the original signed residual at exp(u), exp(u+L) by their power gap. Multiply it by exp(−iwu) and exp(−iv(u−U)/T). Avg is the interval mean of this function over [U,U+T], and Integrable asserts its Lebesgue integrability.

A(m,r,L,w) is the fixed-frequency coefficient. Its zero mode is −c(m). For nonzero w it is −μ(r) times the sum of W(r,L,ρ) over all occurrences with frequency ω(ρ,r)=Im(ρ)/r equal to w. The contribution W(r,L,ρ) is 2r²/[ρ(r−ρ)(r−2ρ)] times (exp((−s+iω(ρ,r))L)−1)/(1−exp(−sL)). Mult is analytic order. The profile K(v) is the integral of exp(−ivt) over [0,1].

The uniform-width Fourier estimate bounds the integral of the modulated residual minus its coefficient on every prefix starting at U. Apply the scalar weighted-primitive bound to the real and imaginary coordinate products. The new phase has modulus one and derivative norm |v|/T. Substituting u=U+Tt in the constant contribution gives K(v). The coefficient identities follow from the uniform-width theorem.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourierResolution.signed_window_even_cutoff_detuned_fourier`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/WeightedPrimitiveBound](../../../../../Arith/Robin/ForwardKernel/WeightedPrimitiveBound.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffUniformWidth](RHMobiusEvenCutoffUniformWidth.md)
