# The arithmetic limsup from a weighted midpoint comparison

## Abstract

Transfer of weighted midpoint estimates to signed prime windows

**Theorem 1.1 (The same remainder profile controls the normalized signed window).**

$$\mathit{RH} \Rightarrow \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\forall E \in \mathbb{R}\to\mathbb{R},\; \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall L \in \mathbb{R},\; \left(0 < L \land L \le \frac{1}{4}\right) \Rightarrow \left(\left(\forall u \in \mathbb{R},\; \left|\operatorname{M}\left(r, u, L\right)\right| \le \operatorname{G}\left(r, L\right) + C \cdot \operatorname{E}\left(L\right)\right) \land \operatorname{G}\left(r, L\right) - C \cdot \operatorname{E}\left(L\right) \le \operatorname{M}\left(r, -\frac{L}{2}, L\right)\right)\right)\right) \Rightarrow \left(\exists C \in \mathbb{R},\; 0 < C \land \left(\forall L \in \mathbb{R},\; \left(0 < L \land L \le \frac{1}{4}\right) \Rightarrow \left(\operatorname{B}\left(m, r, L\right) \land \left|\operatorname{Q}\left(m, r, L\right) - \left|\operatorname{mu}\left(r\right)\right| \cdot \operatorname{G}\left(r, L\right)\right| \le \left|\operatorname{mu}\left(r\right)\right| \cdot C \cdot \operatorname{E}\left(L\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMidpointWindowTransfer.signed_window_midpoint_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M(r,u,L) be the normalized exponential root average on [u,u+L] minus the full root signal at its midpoint. With s=1/2−1/(2r), write G(r,L) for L/(8s) times log(1/L)+log(2r)−2c+1/2 and c=(Euler's constant−1+log(2π))/2.

Q(m,r,L) is the limsup at positive infinity of the absolute original signed residual divided by its power gap, corrected inside the absolute value by μ(m+1)(m+1)/(ms) and μ(r) times the midpoint root signal. B(m,r,L) means the corrected absolute value is eventually bounded.

The whole weighted interval and its midpoint are continuous readouts of the same actual occurrence phase vector. A cofinal return transfers the lower comparison at the origin. The arithmetic term tends to zero after division by the original positive power gap.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMidpointWindowTransfer.signed_window_midpoint_transfer`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement](RHRootLateIncrement.md)
