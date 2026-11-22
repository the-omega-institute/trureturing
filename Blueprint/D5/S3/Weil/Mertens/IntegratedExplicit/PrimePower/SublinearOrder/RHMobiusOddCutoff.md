# Compare neighboring truncation orders

## Abstract

The leading signed prime-window residual at odd cutoff

**Theorem 1.1 (The first omitted arithmetic term).**

$$RH \Rightarrow \left(\exists T \in \mathbb{R},\; \exists K \in \mathbb{R},\; \left(2 \le T \land 0 < K\right) \land \left(\forall m \in \mathbb{N},\; \left(2 \le m \land \operatorname{Odd}\left(m + 1\right)\right) \Rightarrow \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(T \le a \land a \le B\right) \Rightarrow \left(\left|\operatorname{E}\left(m, a, B\right) + \operatorname{mu}\left(m + 1\right) \cdot \frac{m + 1}{m \cdot \operatorname{s}\left(m\right)} \cdot \operatorname{D}\left(\operatorname{s}\left(m\right), a, B\right)\right| \le \operatorname{W}\left(K, m\right) \cdot \operatorname{D}\left(\operatorname{s}\left(m\right) + \operatorname{delta}\left(m\right), a, B\right) \land \operatorname{W}\left(K, m\right) \cdot \operatorname{D}\left(\operatorname{s}\left(m\right) + \operatorname{delta}\left(m\right), a, B\right) \le \operatorname{W}\left(K, m\right) \cdot \frac{\operatorname{s}\left(m\right) + \operatorname{delta}\left(m\right)}{\operatorname{s}\left(m\right)} \cdot a^{-\operatorname{delta}\left(m\right)} \cdot \operatorname{D}\left(\operatorname{s}\left(m\right), a, B\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff.signed_window_odd_cutoff_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write q=m+1, s(m)=1/2−1/q and δ(m)=1/q−1/(q+1). For any rate r the gap D(r,a,B) is a^(−r)−B^(−r). The residual E(m,a,B) subtracts the ordinary spectral endpoint difference and both signed corrections from the original window discrepancy.

For 3≤n≤m the arithmetic correction has coefficient −2μ(n)n²/((n−1)(n−2)) and endpoint difference a^(1/n−1/2)−B^(1/n−1/2). For 2≤n≤m and 2n<m+1 the root correction is −μ(n) times the degree-n root primitive at B minus its value at a. Both spectral sums use actual nontrivial zeros counted with their analytic multiplicities.

For odd q, the retained root degrees at orders m and q agree. The arithmetic sum gains only degree q. The all-order estimate at q therefore bounds the residual after the leading arithmetic term has been removed. The threshold T and multiplier K are common to all odd cutoffs. The weight W(K,m) is Kq(1+log q)². The sharper gap has rate s(m)+δ(m). Integrate the exponential comparison over the closed logarithmic interval to obtain the second inequality. Both include B=a.

**Theorem 1.2 (A lower bound at arbitrarily late starts).**

$$RH \Rightarrow \left(\forall gamma \in \mathbb{R},\; 0 < gamma \Rightarrow \left(\forall K \in \mathbb{R},\; \forall A \in \mathbb{N}\to \mathbb{R},\; \forall N \in \mathbb{N},\; \exists M \in \mathbb{N},\; \operatorname{max}\left(2, N\right) \le M \land \left(\forall m \in \mathbb{N},\; \left(M \le m \land \operatorname{Prime}\left(m + 1\right)\right) \Rightarrow \left(\exists S \in \mathbb{R},\; \operatorname{max}\left(2, \operatorname{A}\left(m\right)\right) \le S \land \left(\forall a \in \mathbb{R},\; \forall B \in \mathbb{R},\; \left(S \le a \land a < B\right) \Rightarrow K \cdot m^{-gamma} \cdot \operatorname{D}\left(\operatorname{s}\left(m\right), a, B\right) < \operatorname{E}\left(m, a, B\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff.signed_window_no_negative_order_exponent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive γ and any real K. Choose one order threshold M such that K m^(−γ)<1 for all m≥M. At each prime q=m+1 in this range the Möbius value is −1 and the leading coefficient exceeds 2.

For each such order, take the start threshold above A(m), 2 and the point where the normalized expansion error drops below 1. The gap is positive for every B>a. The signed residual exceeds the gap on all those windows. Unbounded primes give counterexamples to any uniform negative power, including at any prescribed positive logarithmic width.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff.signed_window_no_negative_order_exponent`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusOddCutoff.signed_window_odd_cutoff_expansion`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHMobiusWindow](../RHMobiusWindow.md)
