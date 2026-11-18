# Sample Covariance Log Energy Refutation

## Abstract

SampleCovarianceLogEnergyRefutation mathematical statements.

**Definition 1.1 (claim).**

$$claim \iff (\forall (\mu : Measure \mathbb{C}), EntryLaw \mu \to (\forall n : \mathbb{N}, penalizedEnergy (meanSpectralMeasure (n + 2) (by omega) \mu) \leq penalizedEnergy (meanSpectralMeasure (n + 1) (by omega) \mu)) \land Tendsto (fun n : \mathbb{N} \mapsto penalizedEnergy (meanSpectralMeasure (n + 1) (by omega) \mu)) atTop (nhds (penalizedEnergy marchenkoPastur)))$$

*Formalization.* `D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.claim` (`✓ std3`).

*Citation.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

Let Xₙ ≔ (ξᵢⱼ)₁≤ᵢ,ⱼ≤ₙ be an n×n random matrix whose entries are i.i.d. centered complex random variables of unit variance, and let μₙ ≔ $\mu_{\frac{1}{n}X_{n}\left(X_{n}\right)^{*}}$ be the corresponding spectral distribution. Is it true that ℰ⁽¹⁾(𝔼μₙ) ↘ ℰ⁽¹⁾(μMP)? PDF p. 4. The law is a measure on Complex; n ranges over Nat and the positive dimensions are n+1 and n+2. The decreasing arrow denotes consecutive nonincrease and convergence. Eigenvalues are counted with multiplicity, and energy is evaluated after taking the mean measure.

**Theorem 1.2 (result).**

$$\neg (\forall (\mu : Measure \mathbb{C}), EntryLaw \mu \to (\forall n : \mathbb{N}, penalizedEnergy (meanSpectralMeasure (n + 2) (by omega) \mu) \leq penalizedEnergy (meanSpectralMeasure (n + 1) (by omega) \mu)) \land Tendsto (fun n : \mathbb{N} \mapsto penalizedEnergy (meanSpectralMeasure (n + 1) (by omega) \mu)) atTop (nhds (penalizedEnergy marchenkoPastur)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-cdy2212q13` (refuted) by `D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-cdy2212q13","declaration_gid":"D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Djalil Chafaï; Benjamin Dadoun; Pierre Youssef (2024). *Monotonicity of the logarithmic energy for random matrices*. DOI: [10.1142/S2010326324500084](https://doi.org/10.1142/S2010326324500084). URL: <https://arxiv.org/abs/2212.06090v2>.

*Commentary.*

result satisfies the displayed statement.

## References

- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.claim`
- Truth anchor: `D5/S3/Analytic/Probability/SampleCovarianceLogEnergyRefutation.result`
- Dependency: [D5/S3/Analytic/Probability/GaussianPolynomialLog](GaussianPolynomialLog.md)
- Dependency: [D5/S3/Analytic/Probability/SampleCovarianceBernoulliOrders](SampleCovarianceBernoulliOrders.md)
- Dependency: [D5/S3/Analytic/Probability/SampleCovarianceSpectralAndSmooth](SampleCovarianceSpectralAndSmooth.md)
- Dependency: [D5/S3/StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality](../../StatisticalMechanics/ParticleProcesses/ExclusionMovingParticleOptimality.md)
