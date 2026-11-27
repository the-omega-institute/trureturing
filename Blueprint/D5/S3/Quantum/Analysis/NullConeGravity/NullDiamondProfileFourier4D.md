# Profiles and radial Fourier weights

## Abstract

Compact cone profiles and their modular frequency representation.

**Definition 1.1 (Separated cone profile).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.ConeProfileTerm`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.ConeProfileTerm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A smooth complex radial function has compact support inside the affine interval (0,1). A complex Lipschitz function on the round sphere supplies its angular dependence.

**Definition 1.2 (Finite cone profile).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.ConeProfile`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.ConeProfile` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A profile is a finite list of separated terms. Its value is the sum of their products.

**Definition 1.3 (Affine profile value).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileValue`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Evaluate the radial and angular factors at their respective coordinates and sum their products.

**Definition 1.4 (Affine radial derivative).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileDeriv`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileDeriv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Differentiate each radial factor and multiply by its angular factor before summing.

**Definition 1.5 (Affine radius).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.affineRadius`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.affineRadius` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The radius is the real sigmoid of 2π times the modular coordinate.

**Definition 1.6 (Weighted Fourier representation).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileEmbed`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileEmbed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the angular-frequency Fourier transform in the modular radial coordinate with unitary normalization, multiply by the square root of the frequency weight, and form a complex L² class on the product phase space.

**Theorem 1.7 (Coth series and signed symbol).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_log_series_symbol`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_log_series_symbol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The symmetric series has constant term 2 and summands with denominator (2π(k+1))² plus the frequency squared. After subtracting the frequency, the series equals the product of the frequency weight and the massless multiplier.

**Theorem 1.8 (Logarithmic Fourier symbol).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_log_fourier_symbol`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_log_fourier_symbol` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Integrate the exponential tail of the real hyperbolic logarithm in the angular Fourier convention. The rational transform, multiplied by the frequency squared divided by π and combined with the linear-distance and sign coefficients, yields the massless symbol.

**Theorem 1.9 (Density in phase space).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileEmbed_dense`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileEmbed_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Translated and dilated compact radial tests separate the weighted Fourier pairing. A countable dense subset of the angular Lipschitz tests separates almost every angular slice. The resulting orthogonal complement is zero.

**Definition 1.10 (Unweighted Fourier profile).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileFourier`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileFourier` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Sum the unitary angular-frequency transforms of the modular radial factors multiplied by their angular factors.

**Theorem 1.11 (Massless spectral pairing).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_nullA_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_nullA_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The pairing with the existing massless multiplier is the integral of the squared modulus of the unweighted Fourier profile against the frequency weight minus the frequency.

**Definition 1.12 (Modular radial slice).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.modularProfile`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.modularProfile` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Evaluate the affine profile at the logistic radius for a fixed angular direction, as a compactly supported Schwartz function.

**Theorem 1.13 (Modular logarithmic pairing).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_modular_log_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_modular_log_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Integrate the radial logarithmic form of each modular slice over the sphere. The linear distance, the decaying logarithmic tail, and the oriented imaginary term combine to give the quadratic form of the massless multiplier.

**Theorem 1.14 (Massive Fourier pairing).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_nullT_pairing`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_nullT_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The square root in each weighted embedding cancels the corresponding denominator of the correction kernel. The resulting integral pairs the unweighted Fourier profiles against the mixed Fourier transform of the correction.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.ConeProfile`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.ConeProfileTerm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.affineRadius`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.modularProfile`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileDeriv`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileEmbed`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileEmbed_dense`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileFourier`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profileValue`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_log_fourier_symbol`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_log_series_symbol`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_modular_log_pairing`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_nullA_pairing`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondProfileFourier4D.profile_nullT_pairing`
- Dependency: [D5/S3/Analytic/CothBernoulliDegree/PartialFraction](../../../Analytic/CothBernoulliDegree/PartialFraction.md)
- Dependency: [D5/S3/Analytic/PetzCothStripMode](../../../Analytic/PetzCothStripMode.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondMultipliers4D](NullDiamondMultipliers4D.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D](NullDiamondSphere4D.md)
