# Weighted phase alignment and the full coefficient

## Abstract

The RH-only left-endpoint limsup formula for the signed prime window

**Theorem 1.1 (Left-endpoint formula and exact equivalence).**

$$\mathit{RH} \Rightarrow \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\operatorname{Eventually}\left((\lambda L \mapsto \operatorname{B}\left(m, r, L\right)), \operatorname{nhdsGT}\left(0\right)\right) \land \left(\operatorname{Tendsto}\left((\lambda L \mapsto \operatorname{A}\left(m, r, L\right) - \operatorname{kappa}\left(m, r\right) \cdot \left(1 - \operatorname{D}\left(\frac{2 \cdot r}{L}\right)\right)), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(0\right)\right) \land \left(\operatorname{mu}\left(r\right) \ne 0 \Rightarrow \left(\operatorname{Tendsto}\left((\lambda L \mapsto \operatorname{A}\left(m, r, L\right)), \operatorname{nhdsGT}\left(0\right), \operatorname{nhds}\left(\operatorname{kappa}\left(m, r\right)\right)\right) \Leftrightarrow \operatorname{Tendsto}\left(D, \mathit{atTop}, \operatorname{nhds}\left(0\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup.signed_window_even_cutoff_weighted_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix natural m and r with m ≥ 2 and m + 1 = 2r. Put s(m) = orderRate(m) = 1/2 − 1/(2r) and cₘ = μ(m+1)(m+1)/(m s(m)). At endpoints exp(u) and exp(u+L), divide signedWindowResidual by powerGap at rate s(m). Add cₘ and μ(r) times the root signal at u. The limsup of the absolute discrepancy as u tends to positive infinity is Qleft(m,r,L). The predicate B(m,r,L) means that the discrepancy is bounded above in absolute value on a late tail. Write A(m,r,L) for Qleft(m,r,L)/(L log²(1/L)) and κ(m,r) for |μ(r)|/(4π s(m)).

For the positive zeta zeros through the inclusive cutoff T, with analytic multiplicities, W(T) is the harmonic mass and P(T) is the real supremum of the corresponding finite weighted sine polynomial. The deficit is D(T) = 1 − P(T)/W(T) where W(T) is positive. The harmonic mass asymptotic gives eventual positivity. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine`

The left discrepancy equals the midpoint discrepancy minus μ(r) times the forward root increment by L/2. Oddness gives a uniform absolute upper bound for the increment. Actual orbit recurrence at each real phase time gives arbitrarily late signed lower estimates. The absolute limsup therefore differs from |μ(r)| (L/s(m)) P(2r/L) by a lower-order error. This comparison also covers μ(r) = 0. `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint` `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup`

The harmonic mass divided by log²(T) tends to 1/(4π). At T = 2r/L the quotient log(T)/log(1/L) tends to one, and P(T)/W(T) lies in [0,1]. This gives the moving-coefficient formula. When μ(r) is nonzero, κ(m,r) is positive. The mutually inverse positive rescalings T = 2r/L and L = 2r/T identify the two limit filters and give the equivalence.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedPhaseLimsup.signed_window_even_cutoff_weighted_phase`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup](RHMobiusEvenCutoffLeftLimsup.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine](RHRootWeightedSine.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffLeftLimsup](RHMobiusEvenCutoffLeftLimsup.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffMidpoint](RHMobiusEvenCutoffMidpoint.md)
- Narrative reference: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootWeightedSine](RHRootWeightedSine.md)
