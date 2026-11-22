# Finite Dimension of the Nonzero Charge Orbit Images

## Abstract

The fixed C2 image of every nonzero Leech charge orbit is finite-dimensional.

**Theorem 1.1 (The whole orbit image lies in the charged span).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbitFinite.leech_charged_orbit_image_le_single_span`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbitFinite.leech_charged_orbit_image_le_single_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pull the span of neutral multiples back to the fixed carrier under the quotient map. It contains the ground and every single oscillator. Every neutral quadratic has its class in the neutral image, so the pullback is stable under all the quadratic (-1)-modes. The charged word induction then puts the entire fixed orbit in the pullback.

**Theorem 1.2 (Each nonzero orbit image is finite-dimensional).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbitFinite.leech_fixed_charge_orbit_image_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbitFinite.leech_fixed_charge_orbit_image_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero Leech charge the orbit image injects as a subspace of the finite-dimensional charged span. This supplies the finite-dimensionality of each nonzero summand in the short charge support.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbitFinite.leech_charged_orbit_image_le_single_span`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbitFinite.leech_fixed_charge_orbit_image_finite`
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedFinite](ActualFixedC2ChargedFinite.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2ChargedOrbit](ActualFixedC2ChargedOrbit.md)
