# Sign certificates for cyclic support

## Abstract

A boundary variation and a finite dual certificate control which cyclic weights are strictly positive.

**Theorem 1.1 (Strict positivity at the outer level).**

$$\operatorname{r}\left(\operatorname{x}\left(i\right)\right) = a + b \cdot \operatorname{x}\left(i\right) + g \cdot \operatorname{x}\left(i\right)^{2}, \left(\left(\left(\forall i \in I,\; \operatorname{x}\left(i\right) \le \operatorname{x}\left(j\right)\right) \land \left(\exists i \in I,\; \operatorname{x}\left(i\right) < \operatorname{x}\left(j\right)\right)\right) \land \left(0 \le g \land \left(\sum_{i}\operatorname{r}\left(\operatorname{x}\left(i\right)\right) = 0 \land 0 < \sum_{i}\operatorname{x}\left(i\right) \cdot \operatorname{r}\left(\operatorname{x}\left(i\right)\right)\right)\right)\right) \Rightarrow 0 < \operatorname{r}\left(\operatorname{x}\left(j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicSupportCertificate.boundary_variation_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let T be the largest of the sampled levels xᵢ, with at least one smaller level. For a quadratic variation with zero total mass and positive first moment, eliminate the constant and linear coefficients using those two moment equations. The remaining quadratic term at T is proportional to the sum over ordered pairs of (xᵢ−xⱼ)²(T−xᵢ)(T−xⱼ). This is the numerator of the monic orthogonal quadratic in the pair-average formula. Each summand is nonnegative, while the first moment term is strictly positive.

**Theorem 1.2 (Exact finite support from two excluded levels).**

$$\operatorname{p}\left(c\right) = a + b \cdot \left(1 - c\right) + g \cdot \frac{1 - c^{2}}{s}, v = \operatorname{Restrict}\left(p, c, S\right), \left(\left(0 < q \land 0 < s\right) \land \left(\left(b \le 0 \land \left(g \le 0 \land \left(\operatorname{p}\left(L\right) < 0 \land \operatorname{p}\left(H\right) < 0\right)\right)\right) \land \left(\left(\forall i \in \operatorname{ZMod}\left(q\right) \setminus S,\; L \le \operatorname{c}\left(i\right) \land \operatorname{c}\left(i\right) \le H\right) \land \left(\left(\forall i \in S,\; 0 < \operatorname{p}\left(\operatorname{c}\left(i\right)\right)\right) \land \left(\sum_{i}\operatorname{v}\left(i\right) = 1 \land \left(\operatorname{M}\left(1, v\right) = alpha \land \operatorname{M}\left(2, v\right) = alpha\right)\right)\right)\right)\right)\right) \Rightarrow \left(v \in \operatorname{Feasible}\left(q, alpha\right) \land \left(\left(\forall w \in \operatorname{Feasible}\left(q, alpha\right),\; w \ne v \Rightarrow \operatorname{E}\left(v\right) < \operatorname{E}\left(w\right)\right) \land \left(\forall w \in \operatorname{Feasible}\left(q, alpha\right),\; \operatorname{IsMinOn}\left(E, \operatorname{Feasible}\left(q, alpha\right), w\right) \Rightarrow \left(\forall i \in \operatorname{ZMod}\left(q\right),\; 0 < \operatorname{w}\left(i\right) \Leftrightarrow i \in S\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CyclicSupportCertificate.exact_support_of_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quadratic has nonpositive coefficients of the two cosine deficits. Its values are positive on the candidate set and negative at both endpoints bounding the excluded cosines. Convexity implies strict negativity at every excluded sample. The candidate equals the positive part of the polynomial and has mass one and the two exact moments. The squared distance to this candidate is strictly positive for any distinct competitor, and the clipping and moment slack terms are nonnegative.

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicSupportCertificate.boundary_variation_pos`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CyclicSupportCertificate.exact_support_of_dual`
- Dependency: [D5/S3/Fourier/Asymptotics/CyclicParityCorrection](CyclicParityCorrection.md)
