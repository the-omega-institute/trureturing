# Physical Generator Locality

## Abstract

Actual tensor currents, charged slices and same-mode jets satisfy uniform finite-difference locality bounds.

**Theorem 1.1 (Current-current locality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_current_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_current_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual current commutator is killed by the second finite difference.

**Theorem 1.2 (Current-charge locality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Ward commutator is killed by one finite difference.

**Theorem 1.3 (Jet-charge locality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A jet of order d has a uniform order d+1 bound against every charged slice.

**Theorem 1.4 (Jet-pair locality).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two jets have the uniform order d_i+d_j+2 bound.

The Ward identity and affine-weight finite-difference recurrence use the canonical same-mode jet formulas and make no positivity or state restriction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_charge_locality`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalCurrent_current_locality`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_charge_locality`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalGeneratorLocality.physicalJet_pair_locality`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateLocality](LatticeAllStateLocality.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling](LatticeHalfFockPhysicalRescaling.md)
