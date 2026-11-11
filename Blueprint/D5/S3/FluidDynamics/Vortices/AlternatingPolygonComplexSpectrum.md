# Alternating Polygon Complex Spectrum

## Abstract

The explicit roots are zero at r=m, plus or minus i*m/sqrt(2) at r=0, plus or minus i*(m-1)/2 at r=1 when this is an internal label, and plus or minus (m-r)*sqrt(r*r-2)/2 at the remaining labels. The neutral guard takes precedence in the dipole. Classification is exhaustive over all complex numbers, with exact algebraic and geometric multiplicities and no collisions between different folded labels.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Definition 1.1 (spectralRoot).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

One square root of each folded spectral value. The neutral label is handled first, so the dipole does not identify its neutral mode with a nonzero internal mode.

**Theorem 1.2 (spectralRoot sq).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot_sq`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Each explicit complex root squares to the corresponding folded squared value.

**Theorem 1.3 (all complex roots).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.all_complex_roots`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.all_complex_roots` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Every complex characteristic root is one of these explicit signed values, and conversely.

**Theorem 1.4 (spectralRoot ne zero).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Every label strictly below the neutral label gives a nonzero complex root.

For m ≥ 1 and folded labels r,s ≤ m, a common signed root μ has μ² equal to both squaredValue m r and squaredValue m s by spectralRoot_sq; the sign disappears on squaring. Injectivity of the real-to-complex embedding gives equality of these real squared values, and AlternatingPolygonMultiplicity.squaredValue_injective gives r = s. Thus different folded labels cannot share a signed root, including the imaginary families and the neutral label. This is a consequence of the existing square and injectivity arguments.

**Theorem 1.5 (signed root multiplicities).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.signed_root_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.signed_root_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Complete nonzero algebraic and geometric multiplicities of both signed roots.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.all_complex_roots`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.signed_root_multiplicities`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot_ne_zero`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum.spectralRoot_sq`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition](AlternatingPolygonDecomposition.md)
