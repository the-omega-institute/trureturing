# Logarithmic power series for the null-diamond correction

## Abstract

Entire power series and the mixed derivative of the four-dimensional null-diamond bulk difference.

For the four-dimensional scalar covariance problem of Satishchandran and Sorce, the bulk difference combines two entire power series and a principal logarithm. Differentiating the product of the null radii times that difference gives the weighted series of the correction.

**Definition 1.1 (Factorial coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.pk`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.pk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each natural k, pₖ = 1/(k!(k+1)!), viewed as a complex number.

**Definition 1.2 (Harmonic coefficient).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.bk`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.bk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each natural k, bₖ = Hₖ + Hₖ₊₁ − 2γ, where H denotes the harmonic numbers and γ is the Euler–Mascheroni constant. The coefficient takes values in ℂ.

**Definition 1.3 (Factorial power series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For complex t, P(t) is the sum over natural k of pₖ tᵏ.

**Definition 1.4 (Harmonic-weighted power series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For complex t, B(t) is the sum over natural k of bₖ pₖ tᵏ.

**Definition 1.5 (Quadratically weighted factorial series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP2`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For complex t, P₂(t) is the sum over natural k of (k+1)² pₖ tᵏ.

**Definition 1.6 (Quadratically weighted harmonic series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB2`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For complex t, B₂(t) is the sum over natural k of ((k+1)² bₖ − 2(k+1)) pₖ tᵏ.

**Definition 1.7 (Bulk difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.bulkDifference`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.bulkDifference` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M and complex q, put t = M²q/4. The bulk difference is M²/(16π²) times (log(t) P(t) − B(t)), with the principal complex logarithm.

**Definition 1.8 (Correction with a supplied logarithm).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correctionLog`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correctionLog` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M and complex t and ℓ, the correction with logarithm ℓ is M²/(16π²) times (ℓ P₂(t) − B₂(t)).

**Definition 1.9 (Boundary correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correction`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correction` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M, u, v and x with x < 1, take t = M²uv(1−x)/2 and use the real logarithm of t, embedded in ℂ, in the correction with a supplied logarithm. The correction is zero for x ≥ 1.

**Theorem 1.10 (The factorial series is entire).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

P is complex differentiable on ℂ. On each bounded disk a factorial majorant controls the series of derivatives.

**Theorem 1.11 (The harmonic-weighted series is entire).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

B is complex differentiable on ℂ. The harmonic numbers grow at most linearly, so their weights still admit a locally uniform factorial majorant.

**Theorem 1.12 (The weighted factorial series is entire).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP2_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP2_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

P₂ is complex differentiable on ℂ. The quadratic weight preserves the local summability of the derivative majorant.

**Theorem 1.13 (The weighted harmonic series is entire).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB2_entire`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB2_entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

B₂ is complex differentiable on ℂ. Split it into the quadratically weighted harmonic series and twice the linearly weighted factorial series.

**Definition 1.14 (Normalized logarithmic series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselSeries`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real t, the normalized series F(t) is 1 + t(log(t) P(t) − B(t)), where log is the real logarithm and all values are combined in ℂ.

**Definition 1.15 (Logarithmic series for the first derivative).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselSeriesSlope`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselSeriesSlope` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real t, the slope series is log(t) P₁(t) + P(t) − B₁(t), where P₁ and B₁ are the series P and B with each coefficient multiplied by k+1.

**Theorem 1.16 (First derivative of the normalized series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.hasDerivAt_besselSeries`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.hasDerivAt_besselSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At every real t > 0, the real derivative of the complex-valued F is the slope series. Differentiate the logarithm and the two power series term by term.

**Theorem 1.17 (Differential equation for the series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.hasDerivAt_besselSeriesSlope`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.hasDerivAt_besselSeriesSlope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At every real t > 0, the real derivative of the complex-valued slope series is F(t)/t. The recurrence of successive factorial coefficients and harmonic numbers gives the coefficient identities.

**Theorem 1.18 (Right limit of the normalized series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.tendsto_besselSeries_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.tendsto_besselSeries_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

F(t) tends to 1 as real t decreases to zero. Use continuity of the two entire series and the vanishing of t log(t).

**Theorem 1.19 (Right limit of the regularized slope).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.tendsto_besselSeriesSlope_sub_log`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.tendsto_besselSeriesSlope_sub_log` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The slope series minus log(t) tends to 2γ as real t decreases to zero. The difference P₁(t) − 1 vanishes to first order, and B₁(0) = 1 − 2γ fixes the limit.

**Theorem 1.20 (Correction as series plus slope).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correctionLog_eq_series`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correctionLog_eq_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M and t, the correction at the real logarithm of t equals M²/(16π²) times the sum of the normalized series and its slope series. Compare the weighted factorial and harmonic coefficients.

**Theorem 1.21 (Mixed derivative in the null radii).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correction_mixed_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correction_mixed_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M, u and v positive and real x < 1, take the u derivative and then the v derivative of uv times the bulk difference at q = 2uv(1−x). Both derivatives are real and take values in ℂ. The resulting mixed derivative is the boundary correction at M, u, v and x.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB2`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB2_entire`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselB_entire`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP2`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP2_entire`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselP_entire`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselSeries`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.besselSeriesSlope`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.bk`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.bulkDifference`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correction`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correctionLog`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correctionLog_eq_series`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.correction_mixed_deriv`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.hasDerivAt_besselSeries`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.hasDerivAt_besselSeriesSlope`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.pk`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.tendsto_besselSeriesSlope_sub_log`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D.tendsto_besselSeries_zero`
