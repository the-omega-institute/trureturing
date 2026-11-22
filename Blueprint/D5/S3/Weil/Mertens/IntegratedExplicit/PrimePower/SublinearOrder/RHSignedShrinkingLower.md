# The signed discrepancy at arbitrarily late starting points

## Abstract

A lower error scale for shrinking signed prime windows

**Theorem 1.1 (Arbitrarily late windows exhibit a logarithmic width error).**

$$\mathit{RH} \Rightarrow \left(\forall m \in \mathbb{N},\; \forall r \in \mathbb{N},\; \left(2 \le m \land \left(m + 1 = 2 \cdot r \land \operatorname{mu}\left(r\right) \ne 0\right)\right) \Rightarrow \left(\exists H \in \mathbb{R},\; \left(0 < H \land H < 1\right) \land \left(\forall d \in \mathbb{R},\; \left(0 < d \land d < \frac{\operatorname{exp}\left(-\left(\frac{1}{2} - \frac{1}{2 \cdot r}\right)\right)}{8 \cdot \left(\frac{1}{2} - \frac{1}{2 \cdot r}\right)}\right) \Rightarrow \left(\forall L \in \mathbb{R},\; \left(0 < L \land L < H\right) \Rightarrow \left(\forall U \in \mathbb{R},\; \exists u \in \mathbb{R},\; U \le u \land d \cdot L \cdot \operatorname{log}\left(\frac{1}{L}\right) \le -\operatorname{mu}\left(r\right) \cdot \left(\operatorname{F}\left(m, u, L\right) + \operatorname{c}\left(m\right) + \operatorname{mu}\left(r\right) \cdot \operatorname{S}\left(r, u\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSignedShrinkingLower.signed_window_even_cutoff_shrinking_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The natural cutoff parameters satisfy q=m+1=2r. The original normalized signed residual F(m,u,L) uses endpoints exp(u), exp(u+L) and the power gap with s=1/2−1/q. Set c(m)=μ(q)q/(ms), and use the centered root spectrum S(r,u) with all analytic zero occurrences.

The imaginary parts of the rational root coefficients give a first moment controlled by the reciprocal-square occurrence mass. The odd part of an increment about zero is bounded linearly. The symmetric cusp then gives a positive one-sided logarithmic lower bound.

Integrate the one-sided bound against the original positive exponential weight and normalize by its mass. For each width the normalized primitive increment and the centered series are continuous readouts of the actual phase orbit. Its late returns preserve a fixed fraction of the origin lower bound.

A single width threshold works for every positive lower coefficient below exp(−s)/(8s).

Choose the late threshold so that the decaying arithmetic remainder is smaller than the retained spectral lower bound. The witnessed residual has sign opposite to the nonzero Möbius coefficient. The witness start can depend on the width and the desired threshold.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSignedShrinkingLower.signed_window_even_cutoff_shrinking_lower`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHMobiusEvenCutoffFourier](RHMobiusEvenCutoffFourier.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootLateIncrement](RHRootLateIncrement.md)
