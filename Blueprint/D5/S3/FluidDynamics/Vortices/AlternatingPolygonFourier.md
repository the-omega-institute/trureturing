# Alternating Polygon Fourier

## Abstract

The coordinate map is an actual linear equivalence: first faithfully relabel the polygon, then use the canonical DFT, and shift the tangential frequency by m. Its action is derived from the existing circulant and inverse-chord transform proofs. No eigenvalue list is assumed.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Definition 1.1 (relabel).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.relabel`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Relabel the existing finite polygon, without changing its cyclic order.

**Definition 1.2 (fourier).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.fourier`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.fourier` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The canonical DFT, after the faithful cyclic relabeling.

**Definition 1.3 (frequencyCoordinates).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.frequencyCoordinates`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.frequencyCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Paired Fourier coordinates. The tangential frequency is shifted by m.

**Theorem 1.4 (frequency block).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.frequency_block`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.frequency_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The actual radial/tangential block action in the complete Fourier coordinates.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.fourier`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.frequencyCoordinates`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.frequency_block`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonFourier.relabel`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes](AlternatingPolygonModes.md)
