# The original physical state Lie algebra

## Abstract

The actual original physical-state quotient carries the zero-mode Lie bracket.

**Theorem 1.1 (Exact quotient representative bracket).**

Lean statement: `D5/S3/VertexAlgebra/Physical/OriginalPhysicalLie.physicalBracket_mk`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Physical/OriginalPhysicalLie.physicalBracket_mk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The quotient is exactly P^1 modulo the image of the actual translation restricted to P^0. The skew primitive is finite and physical, so antisymmetry descends through this exact image. Jacobi is inherited from the actual zero-mode commutator.

This unit formalizes the matter physical-state Lie algebra only. It does not identify it with BRST cohomology or discharge the independent original BRST, HPL, no-ghost, string and AdS/CFT obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Physical/OriginalPhysicalLie.physicalBracket_mk`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualConformalEnergy](../LatticeActualConformalEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualStateDerivative](../LatticeActualStateDerivative.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](../LatticeSugawaraVirasoro.md)
- Dependency: [D5/S3/VertexAlgebra/SourceMobius/Nilpotence](../SourceMobius/Nilpotence.md)
- Dependency: [D5/S3/VertexAlgebra/StateField/SkewSymmetry](../StateField/SkewSymmetry.md)
