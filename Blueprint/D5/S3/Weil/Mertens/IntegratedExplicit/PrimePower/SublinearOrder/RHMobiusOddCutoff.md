# Compare neighboring truncation orders

## Abstract

The leading signed prime-window residual at odd cutoff

**Theorem 1.1 (The first omitted arithmetic term).**

$$RH \Rightarrow \left(\forall m \in \mathbb{N},\; \left(2 \le m \land \operatorname{Odd}\left(m + 1\right)\right) \Rightarrow \left(\exists T \in \mathbb{R},\; \exists C \in \mathbb{R},\; \left(2 \le T \land 0 < C\right) \land \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left|\operatorname{E}\left(m, a, B\right) + \operatorname{mu}\left(m + 1\right) \cdot \frac{m + 1}{m \cdot \operatorname{s}\left(m\right)} \cdot \operatorname{D}\left(m, a, B\right)\right| \le C \cdot a^{-\operatorname{delta}\left(m\right)} \cdot \operatorname{D}\left(m, a, B\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff.signed_window_odd_cutoff_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write q=m+1, s(m)=1/2−1/q and δ(m)=1/q−1/(q+1). The gap D(m,a,B) is a^(−s(m))−B^(−s(m)). The residual E(m,a,B) subtracts the ordinary spectral endpoint difference and both signed corrections from the original window discrepancy.

For 3≤n≤m the arithmetic correction has coefficient −2μ(n)n²/((n−1)(n−2)) and endpoint difference a^(1/n−1/2)−B^(1/n−1/2). For 2≤n≤m and 2n<m+1 the root correction is −μ(n) times the degree-n root primitive at B minus its value at a. Both spectral sums use actual nontrivial zeros counted with their analytic multiplicities.

For odd q, the retained root degrees at orders m and q agree. The arithmetic sum gains only degree q. The all-order estimate at q therefore bounds the residual after the leading arithmetic term has been removed. Its gap uses rate s(m)+δ(m). Integrate the exponential comparison over the closed logarithmic interval to bound the faster gap by ((s(m)+δ(m))/s(m)) a^(−δ(m)) D(m,a,B). The inequality includes B=a.

**Theorem 1.2 (A lower bound at arbitrarily late starts).**

$$RH \Rightarrow \left(\forall gamma \in \mathbb{R},\; \forall K \in \mathbb{R},\; \forall L \in \mathbb{R},\; \left(\left(0 < gamma \land 0 < K\right) \land 0 < L\right) \Rightarrow \left(\forall A \in \mathbb{N}\to \mathbb{R},\; \forall N \in \mathbb{N},\; \exists m \in \mathbb{N},\; \operatorname{max}\left(2, N\right) \le m \land \left(\exists a \in \mathbb{R},\; \operatorname{max}\left(2, \operatorname{A}\left(m\right)\right) \le a \land K \cdot m^{-gamma} \cdot \operatorname{D}\left(m, a, a \cdot \operatorname{exp}\left(L\right)\right) < \left|\operatorname{E}\left(m, a, a \cdot \operatorname{exp}\left(L\right)\right)\right|\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff.signed_window_no_negative_order_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive γ, K and logarithmic width L. The function A can prescribe a lower endpoint threshold separately for each order. Euclid's theorem gives a prime q=m+1 beyond any required order. Its Möbius value is −1 and its leading coefficient exceeds 2.

Choose the prime large enough that K m^(−γ)<1. After fixing the prime, choose a so late that the expansion error divided by D(m,a,B) is below 1. Positive L makes B=a exp(L)>a and the gap strictly positive. The signed residual then exceeds D(m,a,B).

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff.signed_window_no_negative_order_exponent`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff.signed_window_odd_cutoff_expansion`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow](../RHMobiusWindow.md)
