# Contour shifts of the modular Fourier kernel

## Abstract

Horizontal contour translation and exponential Fourier decay of the null-diamond correction.

The separately holomorphic modular kernel in the four-dimensional scalar covariance problem of Satishchandran and Sorce decays along horizontal lines of a strip. Moving the two Fourier contours independently gives enough frequency decay to absorb the inverse quarter-power weights of the covariance.

**Theorem 1.1 (Horizontal contour shift).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.horizontal_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.horizontal_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Let f be a complex-valued function of a complex variable, B ≥ 0 and d > 0 real, with f complex differentiable on the open strip. Suppose for all z in the closed strip that the norm of f(z) is at most B exp(−d |Re z|)(1 + |Re z|). For every real y with |y| ≤ b the integral of f(r) over the real line equals the integral of f(r + iy) over the real line, with respect to Lebesgue measure. Cauchy's rectangle theorem relates the two truncated horizontal integrals to the oriented vertical edges. Their norms tend to zero as the rectangle widens, and the horizontal integrals converge by the exponentially decaying majorant.

**Definition 1.2 (Modular Fourier kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real M, ν, λ and x, the Fourier kernel equals 1/(2π) times the iterated Lebesgue integral over r and s in the real line of exp(−iνr + iλs) G_M(r,s,x), integrating over s first.

**Theorem 1.3 (Joint measurability of the Fourier kernel).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG_measurable`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For each real M, the Fourier kernel as a function of the real triple (ν,λ,x) is measurable. Joint measurability of the integrand and parameterized integration give the conclusion.

**Theorem 1.4 (Uniform exponential decay in both frequencies).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For every real M > 0 there exists a real C > 0 such that for all real ν, λ and x with −1 ≤ x < 1, the norm of the Fourier kernel is at most C exp(−b(|ν| + |λ|)) (1 + |log(1−x)|). The horizontal shifts use the strip edges with imaginary parts opposite in sign to ν and equal in sign to λ, respectively, with either edge available at zero frequency. Integrability permits exchange of the order of integration. The phase on the translated contours then has norm exp(−b(|ν| + |λ|)). The horizontal majorant integrates to a constant times the explicit angular factor. Since b = 3/8 exceeds 1/4, the frequency bound permits multiplication by exp((|ν| + |λ|)/4) while retaining exponential decay.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG_bound`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.fourierG_measurable`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D.horizontal_shift`
- Dependency: [D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability](../../../Analytic/Asymptotics/ExponentialAbsIntegrability.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondBesselStrip4D](NullDiamondBesselStrip4D.md)
