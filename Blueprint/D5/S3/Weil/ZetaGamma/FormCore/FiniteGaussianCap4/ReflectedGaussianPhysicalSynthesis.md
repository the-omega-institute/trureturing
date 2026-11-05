# Actual reflected Gaussian physical synthesis

## Abstract

Actual reflected Gaussian physical synthesis

The actual reflected Gaussian coefficient core and the continuous weighted synthesis are now connected as functions. The same coefficient curve f retains its proved closed-span identity with the actual central-charge kernel. Its graph and absolute Mellin representatives are the normalized reflected Gaussian on the positive half-line.

**Theorem 1.1 (The actual core synthesizes the actual Gaussian).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianPhysicalSynthesis.actual_reflected_gaussian_physical_synthesis`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianPhysicalSynthesis.actual_reflected_gaussian_physical_synthesis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every 0<t<1/36, write a=positiveGaussianSite(t). Both coordinates of synthesis(f(t)) equal gaussianFeature(reflectedSourceCoefficient,reflectedSourceSite(a))/(2 gaussianSiteAmplitude(a)) almost everywhere for their respective measures: (x^(7/2)+x^(15/2)) dx on x>0 and x^(5/4) dx on x>0. The existing Gaussian generating series is even under reflection; reindexing it by n=2k gives the pointwise series with exactly the weighted coefficients of f(t). The synthesis partial sums converge in each Lp space. A subsequence converges almost everywhere, and uniqueness of its pointwise limit identifies the representatives. This reuses the original finite synthesis and its literal representatives; it does not posit a physical realization.

This result supplies the actual coefficient-to-function bridge for the constructed central-charge core. It does not identify that charge with the original H6 full-line mu, prove original-domain surjectivity, establish a closed synthesis image, or resolve RH. The inherited Laguerre polynomial source retains its upstream OpenAI/math attribution and Apache-2.0 notice. This source-relative synthesis theorem makes no literature-priority claim.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianPhysicalSynthesis.actual_reflected_gaussian_physical_synthesis`
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfWeightedSynthesis](LaguerreSevenHalfWeightedSynthesis.md)
- Dependency: [D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianCoefficientCore](ReflectedGaussianCoefficientCore.md)
