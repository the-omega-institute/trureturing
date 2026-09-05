# Golden Archimedean Gap

## Abstract

Every nonzero golden observer mode has one uniform positive Archimedean gap.

**Definition 1.1 (The fundamental golden gap).**

$$\forall sigma: \mathbb{R},\\{}(\operatorname{goldenArchimedeanGap}\left(sigma\right) = \sum_{m=0}^{\infty} \operatorname{log}\left(1 + \frac{{\pi}^{2}}{{\operatorname{log}\left(\phi\right)}^{2} \times {sigma + 2m}^{2}}\right)).$$

*Formalization.* `D5/S3/Weil/ZetaGamma/GoldenArchimedeanGap.goldenArchimedeanGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named gap is the canonical logarithmic Archimedean dispersion evaluated at the squared fundamental golden frequency.

**Lemma 1.2 (The tower is monotone in squared frequency).**

$$\forall sigma: \mathbb{R}, lambda: \mathbb{R}, mu: \mathbb{R},\\{}(0 < sigma, 0 \leq lambda, lambda \leq mu \Rightarrow \operatorname{archimedeanDispersion}\left(sigma, lambda\right) \leq \operatorname{archimedeanDispersion}\left(sigma, mu\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/GoldenArchimedeanGap.archimedean_dispersion_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Termwise logarithmic monotonicity combines with an explicit summable p-series majorant to compare the two infinite towers.

**Theorem 1.3 (All nonzero modes share a positive gap).**

$$\forall sigma: \mathbb{R}, n: \mathbb{Z},\\{}(1 < sigma, \neg n = 0 \Rightarrow \operatorname{archimedeanDispersion}\left(sigma, {(n: \mathbb{R}) \times goldenAngularFrequency}^{2}\right) \geq \operatorname{goldenArchimedeanGap}\left(sigma\right) > 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/GoldenArchimedeanGap.golden_archimedean_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero integer has squared magnitude at least one, so its squared golden frequency dominates the fundamental one.

Dispersion monotonicity gives the uniform lower bound, while the frozen nonzero-mode positivity theorem supplies strict positivity.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/GoldenArchimedeanGap.archimedean_dispersion_mono`
- Truth anchor: `D5/S3/Weil/ZetaGamma/GoldenArchimedeanGap.goldenArchimedeanGap`
- Truth anchor: `D5/S3/Weil/ZetaGamma/GoldenArchimedeanGap.golden_archimedean_gap`
- Dependency: [D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling](../../Observer/GoldenPrimeCircle/GoldenVerticalSampling.md)
- Dependency: [D5/S3/Weil/ZetaGamma/ArchimedeanObserverProductPositive](ArchimedeanObserverProductPositive.md)
