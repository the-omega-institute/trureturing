# Comparing derivatives at equal real parts

## Abstract

Signed Mangoldt moments on a logarithmic window

**Theorem 1.1 (A bound from either sign on the window).**

$$\forall k \in \mathbb{N},\; \forall p \in \mathbb{C},\; \forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall q \in \mathbb{R},\; \forall e \in \mathbb{R},\; 1 < \operatorname{Re}\left(p\right) \Rightarrow \left(0 < a \Rightarrow \left(a \le b \Rightarrow \left(q < \operatorname{Re}\left(p\right) \Rightarrow \left(\left(e = 1 \lor e = -1\right) \Rightarrow \left|\operatorname{D}\left(k, p\right)\right| + e \cdot \operatorname{Re}\left(\operatorname{D}\left(k, \operatorname{Re}\left(p\right)\right)\right) \le 2 \cdot (\operatorname{Re}\left(p\right) - q)^{-k} \cdot \int_{[a,b]} \operatorname{max}\left(e \cdot \operatorname{g}\left(u\right), 0\right) \cdot \operatorname{exp}\left(-\left(q \cdot u\right)\right) du + 2 \cdot \int_{(0,\infty) \setminus [a,b]} \left|\operatorname{g}\left(u\right)\right| \cdot \operatorname{K}\left(k, \operatorname{Re}\left(p\right), u\right) du\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtSignedWindow.signed_window_moment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write D(k,s)=(−1)ᵏΦ₊⁽ᵏ⁾(s)/k! for the normalized derivative of the completed Mangoldt transform, g(u)=U(exp(u)) for the complete remainder, and K(k,σ,u)=uᵏ exp(−σu)/k! for the real moment weight.

The moment at p has modulus at most the integral of |g| against K, where σ is the real part of p. The moment at the real point σ is the signed integral of g against the same weight. For e equal to 1 or −1, their sum with the real term multiplied by e is at most the integral of 2 max(eg,0) against K.

On the prescribed window, the exponential series bounds K by (σ−q)⁻ᵏ exp(−qu). On the complement use max(eg,0)≤|g|. These estimates split the contribution to the same pair of derivatives into a window integral and an absolute tail.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtSignedWindow.signed_window_moment_bound`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtAtOne](CompleteMangoldtAtOne.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtMoments](CompleteMangoldtMoments.md)
