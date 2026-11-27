# Integral normalization of the null-diamond correction

## Abstract

Integral normalization of the logarithmic series and the exact modified Bessel kernel.

The Schwinger integral determines the logarithmic power series in the four-dimensional scalar covariance problem of Satishchandran and Sorce. Its endpoint data fix the solution of the differential equation. Hyperbolic substitutions then give the modified Bessel expression.

**Definition 1.1 (Schwinger integral).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.schwingerH`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.schwingerH` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real t, H(t) is the integral of exp(−s−t/s) with respect to Lebesgue measure over s > 0.

**Theorem 1.2 (Independently normalized power series).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.schwingerH_eq_series`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.schwingerH_eq_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every real t > 0, H(t), viewed in ℂ, equals 1 + t(log(t) P(t) − B(t)). Differentiation under the integral and integration by parts give t H″(t) = H(t). Domination by exp(−s) gives the right limit H(0+) = 1. The substitution s = √t exp(r) makes the first inverse-power moment twice its tail from √t to infinity. Replacing exp(−t/s) by 1 in this tail changes it by at most √t. The tail of exp(−s)/s from d to infinity plus log(d) tends to −γ as d decreases to zero, by integration by parts and the logarithmic integral for the Euler–Mascheroni constant. With d = √t, this gives H′(t) − log(t) tending to 2γ. Recurrence of the power-series coefficients gives the same equation and endpoint data. For the difference, a mean-value estimate gives uniqueness near zero, and ordinary differential equation uniqueness extends the equality to every positive argument.

**Theorem 1.3 (Exact modified Bessel correction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.correction_eq_besselK`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.correction_eq_besselK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M, u and v positive and real x < 1, put z = M√(2uv(1−x)). The correction equals M²/(16π²) times (z K₁(z) − 2 K₀(z)), embedded in ℂ. Here Kν(z) is the integral of exp(−z cosh(s)) cosh(νs) over s > 0. The positive-axis hyperbolic integral identities identify H with z K₁(z) and H′ with −2 K₀(z) when z = 2√t.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.correction_eq_besselK`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.schwingerH`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D.schwingerH_eq_series`
- Dependency: [D5/S3/Analytic/GammaGammaNBU/Result](../../../Analytic/GammaGammaNBU/Result.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselSeries4D](NullDiamondBesselSeries4D.md)
