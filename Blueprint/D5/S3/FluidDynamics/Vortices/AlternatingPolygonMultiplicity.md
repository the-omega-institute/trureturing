# Alternating Polygon Multiplicity

## Abstract

Algebraic multiplicity is computed as polynomial root multiplicity over the complex numbers. Each nonzero matching mode contributes one. The folded fibre count gives multiplicity one at the endpoints and two internally. Collision exclusion consumes the existing positive-root separation proof and separates the nonpositive squared modes. Zero has algebraic multiplicity two for every m at least one.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Definition 1.1 (squaredValue).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.squaredValue`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.squaredValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The squared spectral value of a folded label.

**Theorem 1.2 (squaredValue injective).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.squaredValue_injective`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.squaredValue_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

There are no collisions between different folded squared modes. The positive-positive case consumes the canonical integer separation proof.

**Theorem 1.3 (nonzero algebraic multiplicity).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.nonzero_algebraic_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.nonzero_algebraic_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

A nonzero root has exactly one eigenline in each matching Fourier block; this computes its full algebraic multiplicity, including repeated labels.

**Theorem 1.4 (algebraic multiplicity of mode).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.algebraic_multiplicity_of_mode`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.algebraic_multiplicity_of_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Exact nonzero algebraic multiplicity at a folded squared mode.

**Theorem 1.5 (zero algebraic multiplicity).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.zero_algebraic_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.zero_algebraic_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The zero root has algebraic multiplicity exactly two, including dipole and square.

**Theorem 1.6 (complex root iff mode).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.complex_root_iff_mode`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.complex_root_iff_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Root classification in the complete complex field, before choosing square roots.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.algebraic_multiplicity_of_mode`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.complex_root_iff_mode`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.nonzero_algebraic_multiplicity`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.squaredValue`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.squaredValue_injective`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity.zero_algebraic_multiplicity`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes](AlternatingPolygonModes.md)
