# CompositionZeroFree

## Abstract

Every positive-composition normalized source series is zero-free on the unit disk.

**Theorem 1.1 (The complete source-specific disk consumer).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFree.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFree.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Acknowledgement.* Sanford S. Miller, Petru T. Mocanu, and Maxwell O. Reade (1978). *Starlike integral operators*. DOI: [10.2140/pjm.1978.79.157](https://doi.org/10.2140/pjm.1978.79.157). URL: <https://msp.org/pjm/1978/79-1/pjm-v79-n1-p13-p.pdf>.

*Commentary.*

For every head:PNat and tail:List PNat, let d=tail.length+1 and F(z)=sum_n (H(tail,n+d-1)/(n+d)^head) z^n. Set L(z)=z^d F(z), Q(0)=d, and Q(z)=z L'(z)/L(z) away from zero. The defining F series is absolutely convergent for every |z|<1. Both F and Q are analytic on that disk, F never vanishes there, and Re Q is strictly positive everywhere, including zero. There are no additional recurrence, coefficient estimate, analyticity, first-contact or zero-freeness assumptions.

The proof keeps the classical first-contact argument local: a compact minimal contact radius, the angular derivative and the inward radial derivative contradict the normalized differential equation. The quotient g/h is formed using only the induction hypothesis that h is nonzero; nonvanishing of g is a conclusion. Induction on the tail and the positive head uses the two actual source recurrences. Continuity extends the normalized equation at zero, and a direct derivative calculation identifies the explicitly extended Q.

This is an intermediate disk theorem toward Xu-Zhao Conjecture 1.3. It makes no full-conjecture resolution or originality claim and receives zero solved-problem credit. Boundary convergence, slit continuation, bank estimates, formal-inverse coefficient realization and finite-contour sign transfer remain separate obligations. No global slit zero-freeness or univalence for depth greater than one is asserted.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFree.result`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences](CompositionRecurrences.md)
