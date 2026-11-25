# The triangular average at the actual zeta zeros

## Abstract

A positive weighted Fejér margin for the Mangoldt remainder

**Theorem 1.1 (A lower bound for the weighted transform).**

$$\operatorname{RiemannHypothesis} \Rightarrow \left(\exists delta \in \mathbb{R},\; 0 < delta \land \left(\exists T \in \mathbb{R},\; \forall y \in \mathbb{R},\; T \le y \Rightarrow delta \cdot \operatorname{q}\left(y\right) \cdot y^{2} \le \operatorname{W}\left(y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerWeightedMargin.eventually_positive_triangular_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write q(y) = exp(−y/2). For the k-th actual zero occurrence, let γₖ be its ordinate and aₖ its actual explicit-formula coefficient. The function W(y) sums |aₖ|(1 − cos(γₖy)) sinc²(q(y)yγₖ/4) over all k in ℕ. Under RH, conjugation pairs the contributions at positive and negative ordinates. The weight on a positive ordinate γ of multiplicity m is 2m(1 − cos(γy))/(1/4 + γ²) and the triangular factor is sinc²(qyγ/4).

The unweighted phase deficit is eventually at least qy²/64. The reciprocal-square tail bound makes the weight beyond a fixed cutoff in the scaled ordinate qyγ at most qy²/192. The cumulative zero count bounds the total weight in sufficiently narrow bands around the finitely many positive zeros of the triangular factor below that cutoff by another qy²/192. On the remaining compact set the factor has a positive minimum. Multiplying by the remaining weight gives one positive constant δ valid on a common real tail.

**Theorem 1.2 (A squared-logarithm coefficient strictly above one forty-eighth).**

$$\operatorname{RiemannHypothesis} \Leftrightarrow \left(\exists c \in \mathbb{R},\; \frac{1}{48} < c \land \left(\exists T \in \mathbb{R},\; \forall x \in \mathbb{R},\; T \le x \Rightarrow \operatorname{U}\left(x\right) \le firstLiMass \cdot \sqrt{x} - c \cdot \operatorname{log}\left(x\right)^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerWeightedMargin.rh_iff_eventually_weighted_fejer_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is CompleteMertensPeak.U and the leading constant is firstLiMass. Average the uniform midpoint inequality against the triangular probability law on [0, 1/2]. Its averages of b and b/2 − b² are 1/6 and 1/24. The spectral side leaves the weighted transform as a positive correction to the leading coefficient 1/48 after dividing the inequality by two.

The error terms are o(qy²), so the forward implication keeps half the margin δ. Setting y = log x gives the eventual envelope with c = 1/48 + δ/2. Conversely, a bound with one such c implies the bounds for every coefficient below 1/48 because the squared logarithm is nonnegative. The finite Fejér criterion then gives RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerWeightedMargin.eventually_positive_triangular_margin`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerWeightedMargin.rh_iff_eventually_weighted_fejer_gap`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerActualOrdinates](MangoldtFejerActualOrdinates.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtUniformFejerGap](MangoldtUniformFejerGap.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement](PrimePower/SublinearOrder/RHRootQuarterPhaseIncrement.md)
- Dependency: [D5/S3/Weil/ZeroData/PositiveOrdinateSpectrum](../../ZeroData/PositiveOrdinateSpectrum.md)
