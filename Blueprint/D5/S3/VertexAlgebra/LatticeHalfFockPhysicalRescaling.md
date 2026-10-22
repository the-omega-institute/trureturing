# Signed Physical Slices and Jets

## Abstract

The canonical half-Fock normal field admits signed physical slices and same-mode jets on the actual tensor module.

The slice at an integer shift is the coefficient reindexing field.coeff (2*mode-shift). Its singleton insertion at shift s+2*d+1 is the ordinary normalMinusOne of the canonical jet and the slice at s, proved pointwise by the exhaustive signed mode split.

**Theorem 1.1 (Slice mode formula).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The physical slice mode is the native field coefficient at -2*mode-shift-2.

**Theorem 1.2 (Jet mode formula).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalJet_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalJet_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The physical jet mode is the canonical same-mode jet current.

**Theorem 1.3 (Singleton physical slice bridge).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_singletonLinear`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_singletonLinear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After fixing the actual tensor vector, the signed finite support partition gives the normalMinusOne bridge.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalJet_mode`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_mode`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockPhysicalRescaling.physicalSlice_singletonLinear`
- Dependency: [D5/S3/VertexAlgebra/FieldNormalProduct](FieldNormalProduct.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTranslation](LatticeHalfFockOriginalTranslation.md)
