# Phase recurrence and the arithmetic remainder

## Abstract

The midpoint limsup of the signed shrinking prime window

**Theorem 1.1 (Finite two-term midpoint limsup under RH).**

$$\mathit{RH} \Rightarrow \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall L \in \mathbb{R},\; \left(0 < L \land L \le \frac{1}{4}\right) \Rightarrow \left(\operatorname{B}\left(m, r, L\right) \land \left|\operatorname{Q}\left(m, r, L\right) - \left|\operatorname{mu}\left(r\right)\right| \cdot \operatorname{G}\left(r, L\right)\right| \le \left|\operatorname{mu}\left(r\right)\right| \cdot \operatorname{E}\left(C, L\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint.signed_window_even_cutoff_midpoint_limsup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be the original signed prime window divided by its power gap. For m+1=2r put s=1/2−1/(2r) and cₘ=μ(m+1)(m+1)/(ms). Define Q(m,r,L) as the limsup as u tends to positive infinity of the absolute value of F(m,L,u)+cₘ+μ(r)S(r,u+L/2), where S is the full actual-occurrence root spectrum. B(m,r,L) means this function of u is eventually bounded above. Its values are nonnegative.

The exponential window and midpoint are read from the same phase vector. Summable coefficient norms give uniform convergence of the readout, and parameter continuity of the integral gives one late return for the entire window. The decay estimate for the arithmetic remainder after division by the power gap transfers the spectral upper bound and that late lower bound to the original window.

Write G(r,L) for L/(8s) times log(1/L)+log(2r)−2c+1/2, with c=(Euler's constant−1+log(2π))/2, and E(C,L)=C L²(1+log(1/L))². The error vanishes when μ(r)=0.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint.signed_window_even_cutoff_midpoint_limsup`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootMidpointAverage](RHRootMidpointAverage.md)
