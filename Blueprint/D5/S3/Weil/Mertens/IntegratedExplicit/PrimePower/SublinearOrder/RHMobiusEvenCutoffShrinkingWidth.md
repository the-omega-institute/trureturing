# Shrinking logarithmic widths

## Abstract

The centered root spectrum on shrinking signed prime windows

**Theorem 1.1 (The centered root spectrum is recovered uniformly in the late start).**

$$\mathit{RH} \Rightarrow \left(\exists U \in \mathbb{R},\; 0 < U \land \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land m + 1 = 2 \cdot r\right) \Rightarrow \left(\left(\forall u \in \mathbb{R},\; \forall L \in \mathbb{R},\; 0 < L \Rightarrow \operatorname{P}\left(r, u, L\right) = \operatorname{A}\left(r, u, L\right)\right) \land \left(\exists K \in \mathbb{R},\; 0 < K \land \left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\exists H \in \mathbb{R},\; 0 < H \land \left(\forall u \in \mathbb{R},\; \forall L \in \mathbb{R},\; \left(U \le u \land \left(0 < L \land L < H\right)\right) \Rightarrow \left|\operatorname{F}\left(m, u, L\right) + \operatorname{c}\left(m\right) + \operatorname{mu}\left(r\right) \cdot \operatorname{S}\left(r, u\right)\right| \le e + K \cdot \operatorname{exp}\left(-\left(\operatorname{delta}\left(m\right) \cdot u\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingWidth.signed_window_even_cutoff_shrinking_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put q=m+1=2r, s=1/2−1/q, δ=1/q−1/(q+1) and c(m)=μ(q)q/(m s). F(m,u,L) is the original signed residual for exp(u), exp(u+L), divided by its power gap. P(r,u,L) is the root-primitive increment at the same endpoints divided by the same gap.

S(r,u) is the real part of the sum over all actual zero occurrences of rootCoeff(r,k) exp((ρₖ−1/2)u/r), divided by s. A(r,u,L) is the integral of exp(−st) S(r,u+t) over [0,L] divided by the integral of exp(−st) over the same interval. The denominator is positive for L>0.

The known integral of the root density gives the primitive increment. Removing its exponential decay yields the positive normalized average of the centered series. Under RH, each centered mode is uniformly continuous and bounded in modulus by its coefficient. The summable coefficient bound passes uniform continuity to the full series. The weighted mean value theorem identifies the average with a value of the series within the window. Its modulus controls the error at that point, and the even-cutoff expansion supplies the decaying arithmetic remainder.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffShrinkingWidth.signed_window_even_cutoff_shrinking_width`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoff](RHMobiusEvenCutoff.md)
