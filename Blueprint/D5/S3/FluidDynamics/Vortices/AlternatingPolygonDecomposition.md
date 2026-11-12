# Alternating Polygon Decomposition

## Abstract

The inverse coordinate equivalence injects each complete two-dimensional Fourier block into actual Cartesian space. The restriction theorem records its action. Reconstruction and uniqueness certify the complete invariant direct sum. Nonzero geometric multiplicities follow from equality of generalized and ordinary eigenspaces and the characteristic polynomial multiplicities.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

The canonical DFT uses the negative character in the forward transform and the positive character divided by N in its inverse. Thus a unit coordinate of the injected block gives the source vector f^q/N in the radial slot and f^(q+m)/N in the tangential slot. These have exactly the source invariant span U_q; the common nonzero factor 1/N preserves its restriction matrix. The paired tangential index is reduced modulo N=2m.

**Definition 1.1 (block).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.block`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.block` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Injection of the entire two-dimensional Fourier block into actual Cartesian space.

**Theorem 1.2 (coordinates block).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.coordinates_block`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.coordinates_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The complete Cartesian coordinate equivalence sends a block injection to its single Fourier coordinate.

**Theorem 1.3 (block restriction).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.block_restriction`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.block_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The actual restriction action on each block, including the neutral block.

**Theorem 1.4 (reconstruct).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.reconstruct`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.reconstruct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Completeness: every Cartesian displacement is the sum of its actual invariant blocks.

**Theorem 1.5 (unique coefficients).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.unique_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.unique_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Directness: the complete block expansion has unique coefficients.

**Definition 1.6 (invariantSpace).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.invariantSpace`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.invariantSpace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The actual invariant subspace belonging to a single Fourier label.

**Theorem 1.7 (invariantSpace finrank).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.invariantSpace_finrank`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.invariantSpace_finrank` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Each actual Cartesian Fourier block has complex dimension two.

**Theorem 1.8 (geometric eq algebraic).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.geometric_eq_algebraic`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.geometric_eq_algebraic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

All complex nonzero geometric multiplicities equal the full algebraic multiplicities.

**Theorem 1.9 (geometric multiplicity of mode).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.geometric_multiplicity_of_mode`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.geometric_multiplicity_of_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Exact geometric multiplicity at each folded label, with all collisions counted.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.block`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.block_restriction`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.coordinates_block`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.geometric_eq_algebraic`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.geometric_multiplicity_of_mode`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.invariantSpace`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.invariantSpace_finrank`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.reconstruct`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonDecomposition.unique_coefficients`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonJordan](AlternatingPolygonJordan.md)
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonMultiplicity](AlternatingPolygonMultiplicity.md)
