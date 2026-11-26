# The quantitative shrinking-width estimate

## Abstract

An explicit error in the shrinking logarithmic width

**Theorem 1.1 (A logarithmic-square width bound for the original signed prime window).**

$$\mathit{RH} \Rightarrow \left(\exists U \in \mathbb{R},\; 0 < U \land \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\exists C \in \mathbb{R},\; \exists K \in \mathbb{R},\; 0 < C \land \left(0 < K \land \left(\forall u \in \mathbb{R},\; \forall L \in \mathbb{R},\; \left(U \le u \land \left(0 < L \land L \le \frac{1}{4}\right)\right) \Rightarrow \left|\operatorname{F}\left(m, u, L\right) + \operatorname{c}\left(m\right) + \operatorname{mu}\left(r\right) \cdot \operatorname{S}\left(r, u\right)\right| \le C \cdot L \cdot \left(1 + \operatorname{log}\left(\frac{1}{L}\right)\right) \cdot \left(1 + \operatorname{log}\left(\frac{1}{L}\right)\right) + K \cdot \operatorname{exp}\left(-\left(\operatorname{delta}\left(m\right) \cdot u\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingRate.signed_window_even_cutoff_shrinking_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put q=m+1=2r, s=1/2−1/q, δ=1/q−1/(q+1) and c(m)=μ(q)q/(m s). F(m,u,L) is the original signed residual for exp(u), exp(u+L) divided by its power gap. S(r,u) is the real part of the sum over all actual zero occurrences of rootCoeff(r,k) exp((ρₖ−1/2)u/r), divided by s.

For shifts of size at most L, split the series at ordinate height 1/L. The phase increment on the low side is bounded by the frequency times the shift. One factor of height cancels in the coefficient denominator. The truncated reciprocal moment bounds this part. On the high side the phase difference is at most two, and the inverse-square tail applies.

The normalized root increment equals the value of the centered signal at some point of the logarithmic window. The same modulus bounds the difference from the left endpoint. Dividing the even-cutoff expansion by the power gap retains its exponential arithmetic remainder.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingRate.signed_window_even_cutoff_shrinking_rate`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingWidth](RHMobiusEvenCutoffShrinkingWidth.md)
