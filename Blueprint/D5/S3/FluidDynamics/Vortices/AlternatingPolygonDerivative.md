# Alternating Polygon Derivative

## Abstract

Differentiability is proved on the collision-free domain. Each reported partial derivative is a coordinate of the Frechet derivative applied to the corresponding coordinate direction. Finite linear reconstruction identifies the full derivative with matrix multiplication. This bridge connects the canonical normalized matrix and all physical parameter matrices to the actual field.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Theorem 1.1 (jacobian entry).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.jacobian_entry`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.jacobian_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Every reported matrix entry is a coordinate of the genuine derivative.

**Theorem 1.2 (fderiv eq mulVec).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.fderiv_eq_mulVec`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.fderiv_eq_mulVec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The full derivative acts by the actual Cartesian Jacobian on every direction.

**Theorem 1.3 (hasFDerivAt field).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.hasFDerivAt_field`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.hasFDerivAt_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

A kernel-checked Frechet derivative, with no spectral or matrix assumption.

**Theorem 1.4 (hasFDerivAt normalized).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.hasFDerivAt_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.hasFDerivAt_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The canonical normalized matrix is the matrix of this same genuine derivative.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.fderiv_eq_mulVec`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.hasFDerivAt_field`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.hasFDerivAt_normalized`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDerivative.jacobian_entry`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonParameters](AlternatingPolygonParameters.md)
