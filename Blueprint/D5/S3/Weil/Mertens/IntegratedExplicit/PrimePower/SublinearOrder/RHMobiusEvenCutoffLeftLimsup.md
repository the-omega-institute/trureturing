# The signed shrinking prime window at its left endpoint

## Abstract

The exact left-endpoint limsup scale of the original signed prime window

**Theorem 1.1 (Finite late limsup and its sharp coefficient).**

$$\left(\mathit{RH} \land q \in H\right) \Rightarrow \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\operatorname{Eventually}\left((\lambda L \mapsto \operatorname{B}\left(m, r, L\right)), \operatorname{nhdsGT}\left(0\right)\right) \land \operatorname{Tendsto}\left((\lambda L \mapsto \frac{\operatorname{Q}\left(m, r, L\right)}{L \cdot \operatorname{log}\left(\frac{1}{L}\right)^{2}}), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(\frac{\left|\operatorname{mu}\left(r\right)\right|}{4 \cdot \pi \cdot \operatorname{s}\left(m\right)}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup.signed_window_even_cutoff_left_limsup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume Mathlib's Riemann hypothesis RH and q in H, where q is the constant phase i on the distinct positive zeta zeros and H is their product-topology phase hull. For m ≥ 2 and m + 1 = 2r, set s(m) = orderRate(m) = 1/2 − 1/(2r) and cₘ = μ(m+1)(m+1)/(m s(m)). `D5/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer`

Let F(m,L,u) be signedWindowResidual at the endpoints exp(u) and exp(u+L), divided by powerGap with rate s(m) at the same endpoints. Write Q(m,r,L) for the limsup as u tends to positive infinity of |F(m,L,u) + cₘ + μ(r) S(r,u)|. The signal S counts the full actual zero occurrences with analytic multiplicity. B(m,r,L) means that the same absolute discrepancy is bounded above on a late tail. The width filter is the right-hand neighborhood filter at zero.

The left discrepancy equals the midpoint discrepancy minus μ(r) times the forward displacement of the root signal by L/2. The midpoint limsup controls the contribution of the midpoint discrepancy at lower order. The signed quarter-phase returns give the reverse bound for the absolute limsup. If μ(r) = 0, the midpoint estimate makes that limsup zero for small widths. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint` `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement`

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup.signed_window_even_cutoff_left_limsup`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint](RHMobiusEvenCutoffMidpoint.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement](RHRootQuarterPhaseIncrement.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint](RHMobiusEvenCutoffMidpoint.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement](RHRootQuarterPhaseIncrement.md)
- Narrative reference: [D5/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer](../../../../ZeroData/ZetaOrdinateCompleteOptimizer.md)
