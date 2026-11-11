# Charged native creation reconstruction

## Abstract

LatticeCosetGroundReconstruction

**Theorem 1.1 (ground_reconstruction).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetGroundReconstruction.ground_reconstruction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetGroundReconstruction.ground_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original native lattice D, every finite external rank, integral B, symmetric even-diagonal C, arbitrary integral external source and target charges a,d, original integral source charge n, integer mode m and arbitrary original target state g, actualField at the lifted charge (n,a), applied in mode m to J(d,g), equals the natural-index finite sum of mixedState in sector a+d with j-th external creation coefficient and the actual projected mode m+j on J(d,g). Both ranks may be zero. Neither original nor ambient positivity is required for this charged identity. The native finite annihilation polynomial has longitudinal coefficients. Splitting the full creation exponential coefficient and applying its finite polynomial convolution proves reconstruction while retaining the literal native epsilon and full integer charge pairing.

Bakalov-Kac, math/0402315v1, section 4.1, supplies the charged field convention. The scalar sign and zero-mode exponent stay inside the native actualField; there is no cocycle on rational charges. This charged calculation is consumed by the all-source normal-product induction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetGroundReconstruction.ground_reconstruction`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation](LatticeCosetCreationSeparation.md)
