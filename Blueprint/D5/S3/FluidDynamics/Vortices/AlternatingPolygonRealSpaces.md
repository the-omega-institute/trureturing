# Alternating Polygon Real Spaces

## Abstract

The original real Cartesian operator embeds faithfully into its complexification. Nonzero semisimplicity descends to the real operator. The stable and unstable spaces are the spectral sums of the actual negative and positive real eigenspaces. Injectivity of these sums follows from independence of distinct eigenspaces; each sign has dimension 2*(m-2), rather than merely m-2 distinct spectral values.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Definition 1.1 (realOperator).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.realOperator`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.realOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The canonical Cartesian Jacobian acts on the original real displacement space.

**Definition 1.2 (complexify).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The faithful real inclusion into the actual complexified Cartesian space.

**Theorem 1.3 (complexify injective).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify_injective`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The coordinatewise real inclusion into the complex displacement space is injective.

**Theorem 1.4 (complexify operator).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify_operator`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify_operator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The real inclusion intertwines the original real Jacobian and its actual complexification.

**Theorem 1.5 (real nonzero semisimple).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.real_nonzero_semisimple`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.real_nonzero_semisimple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Nonzero semisimplicity also holds over the original real displacement space.

**Theorem 1.6 (real geometric multiplicity).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.real_geometric_multiplicity`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.real_geometric_multiplicity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Every signed real root has a two-dimensional real eigenspace.

**Definition 1.7 (spectralSum).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.spectralSum`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.spectralSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The ordinary spectral sum for one sign; each summand is an actual real eigenspace.

**Definition 1.8 (unstableSpace).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.unstableSpace`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.unstableSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The positive real spectral space is the range of the sum of actual positive eigenspaces.

**Definition 1.9 (stableSpace).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.stableSpace`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.stableSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The negative real spectral space is the range of the sum of actual negative eigenspaces.

**Theorem 1.10 (unstable finrank).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.unstable_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.unstable_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

For m at least three the actual positive real spectral space has dimension 2*(m-2).

**Theorem 1.11 (stable finrank).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.stable_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.stable_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

For m at least three the actual negative real spectral space has dimension 2*(m-2).

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify_injective`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.complexify_operator`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.realOperator`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.real_geometric_multiplicity`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.real_nonzero_semisimple`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.spectralSum`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.stableSpace`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.stable_finrank`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.unstableSpace`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonRealSpaces.unstable_finrank`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonComplexSpectrum](AlternatingPolygonComplexSpectrum.md)
