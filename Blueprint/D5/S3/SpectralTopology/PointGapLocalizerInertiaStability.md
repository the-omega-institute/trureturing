# Point-Gap Localizer Inertia Stability

## Abstract

Quantitative Weyl certificates keep point-gap localizer inertia constant along an admissible radial path.

**Definition 1.1 (Localizer position perturbation).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.localizerPositionPerturbation`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.localizerPositionPerturbation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real position scale multiplies the Hermitian block-diagonal position direction.

**Definition 1.2 (Localizer Weyl certificate).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.HasLocalizerWeylCertificate`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.HasLocalizerWeylCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A one-scale certificate combines the zero-scale threshold gap with a perturbation radius bound.

**Definition 1.3 (Uniform radial Weyl certificate).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.HasUniformRadialLocalizerWeylCertificate`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.HasUniformRadialLocalizerWeylCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The threshold gap is fixed at zero scale while the perturbation radius is certified along the unit segment.

**Definition 1.4 (Radial localizer signature).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radialLocalizerSignature`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radialLocalizerSignature` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite localizer signature is evaluated at the contracted scale along the radial path.

**Theorem 1.5 (Hermitian localizer perturbation).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.localizer_position_perturbation_isHermitian`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.localizer_position_perturbation_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real scale and Hermitian position observable give a Hermitian position perturbation.

**Theorem 1.6 (Endpoint inertia transport).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_inertia_eq_zero_scale_of_weyl_certificate`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_inertia_eq_zero_scale_of_weyl_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An admissible scale and localizer Weyl certificate identify finite-scale inertia with zero-scale inertia.

**Theorem 1.7 (Exact finite-scale inertia).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_exact_inertia_of_weyl_certificate`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_exact_inertia_of_weyl_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A point gap upgrades the transported endpoint inertia to exact half-dimensional positive and negative counts.

**Theorem 1.8 (Finite-scale signature vanishing).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_signature_eq_zero_of_weyl_certificate`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_signature_eq_zero_of_weyl_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite localizer signature vanishes under the same quantitative Weyl certificate.

**Theorem 1.9 (Uniform radial inertia).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radial_localizer_exact_inertia_of_uniform_weyl_certificate`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radial_localizer_exact_inertia_of_uniform_weyl_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A uniform radial certificate gives exact inertia at every point of the admissible unit segment.

**Theorem 1.10 (Uniform radial signature vanishing).**

Lean statement: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radial_localizer_signature_eq_zero_of_uniform_weyl_certificate`

*Formalization.* `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radial_localizer_signature_eq_zero_of_uniform_weyl_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A uniform radial certificate makes the finite localizer signature zero throughout the path.

## References

- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.localizerPositionPerturbation`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.HasLocalizerWeylCertificate`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.HasUniformRadialLocalizerWeylCertificate`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radialLocalizerSignature`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.localizer_position_perturbation_isHermitian`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_inertia_eq_zero_scale_of_weyl_certificate`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_exact_inertia_of_weyl_certificate`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.finite_localizer_signature_eq_zero_of_weyl_certificate`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radial_localizer_exact_inertia_of_uniform_weyl_certificate`
- Truth anchor: `D5/S3/SpectralTopology/PointGapLocalizerInertiaStability.radial_localizer_signature_eq_zero_of_uniform_weyl_certificate`
- Dependency: [D5/S3/SpectralTopology/PointGapRadialGapPath](PointGapRadialGapPath.md)
- Dependency: [D5/S3/SpectralTopology/FiniteHermitianInertiaStability](FiniteHermitianInertiaStability.md)
- Dependency: [D5/S3/SpectralTopology/PointGapExactInertia](PointGapExactInertia.md)
