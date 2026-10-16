# Dimension-sixteen spectral purity by interpolation

## Abstract

The two qutrit boundary constraints imply the sharp dimension-sixteen spectral purity estimate.

**Definition 1.1 (The first dimension-sixteen boundary matrix).**

$$\forall (l:Fin\left(16\right)\to \mathbb{R}), K1\left(l\right)=!![2\cdot l\left(15\right),l\left(14\right)-l\left(0\right),l\left(12\right)-l\left(1\right);l\left(14\right)-l\left(0\right),2\cdot l\left(13\right),l\left(11\right)-l\left(2\right);l\left(12\right)-l\left(1\right),l\left(11\right)-l\left(2\right),2\cdot l\left(10\right)]$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound.K1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a descending sixteen-coordinate spectrum, retain the largest three and smallest six values in the first qutrit boundary matrix. Indices are zero-based. These constraints are necessary for literal four-by-four APPT via QuadbitSpectralReduction; sufficiency is not claimed.

**Definition 1.2 (The second dimension-sixteen boundary matrix).**

$$\forall (l:Fin\left(16\right)\to \mathbb{R}), K2\left(l\right)=!![2\cdot l\left(15\right),l\left(14\right)-l\left(0\right),l\left(13\right)-l\left(1\right);l\left(14\right)-l\left(0\right),2\cdot l\left(12\right),l\left(11\right)-l\left(2\right);l\left(13\right)-l\left(1\right),l\left(11\right)-l\left(2\right),2\cdot l\left(10\right)]$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound.K2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second real symmetric boundary matrix exchanges spectral indices 12 and 13 relative to the first. Both matrices enter the interpolation certificate.

**Theorem 1.3 (The sharp sixteen-coordinate spectral estimate).**

$$\forall (l:Fin\left(16\right)\to \mathbb{R}), ((Antitone\left(l\right))\land (\forall (i:Fin\left(16\right)), 0\leq l\left(i\right))\land (\sum_{i:Fin\left(16\right)} l\left(i\right)=1)\land (Matrix.PosSemidef\left(K1\left(l\right)\right))\land (Matrix.PosSemidef\left(K2\left(l\right)\right)))\Rightarrow \sum_{i:Fin\left(16\right)} (l\left(i\right))^{2}\leq \frac{2}{27}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound.spectral_purity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every antitone nonnegative real sixteen-coordinate vector of mass one with K1 and K2 positive semidefinite, its square sum is at most 2/27. Let t be coordinate 9. Testing K1 on the all-ones vector bounds the largest-three sum by the smallest-six sum and gives t at most 1/13. If t is at most 1/18, insert two copies of t into the middle, divide by mass 1+2t, and apply QutritN6PurityBound.certificate_bound. Otherwise delete coordinate 9, divide by mass 1-t, and apply QutritN5PurityBound.certificate_bound. Both transformations preserve the boundary matrices up to a positive scalar. Their square sums are respectively P+2t² and P-t²; two exact quadratic inequalities yield 2/27, meeting at t=1/18. No APPT sufficiency statement, physical preparation, or experiment is assumed. QuadbitMaximumPurity consumes the result after the genuine local-corner spectral reduction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound.K1`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound.K2`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitSpectralPurityBound.spectral_purity_bound`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN5PurityBound](QutritN5PurityBound.md)
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritN6PurityBound](QutritN6PurityBound.md)
