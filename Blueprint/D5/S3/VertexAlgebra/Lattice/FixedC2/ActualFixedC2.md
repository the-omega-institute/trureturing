# The Intrinsic Lattice Fixed C2 Span

## Abstract

The intrinsic C2 span of the actual sign-fixed lattice vertex algebra.

The lattice data consist of a natural-number rank and a symmetric integral Gram matrix with even diagonal. The actual complex carrier consists of finitely supported charge families of oscillator polynomials.

**Definition 1.1 (The intrinsic fixed C2 span).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2.fixedC2`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2.fixedC2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed space consists of the states fixed by the lattice sign involution. The intrinsic C2 submodule is the complex span in that space of the restricted actual (-2)-products of pairs of fixed states. The intrinsic quotient is the fixed space modulo this span.

**Theorem 1.2 (Translation of a fixed state).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2.translation_mem_fixedC2`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2.translation_mem_fixedC2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The translation of every fixed state lies in the intrinsic C2 span. It is the fixed (-2)-product of that state with the fixed vacuum.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2.fixedC2`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/FixedC2/ActualFixedC2.translation_mem_fixedC2`
- Dependency: [D5/S3/VertexAlgebra/LatticeInvolution](../../LatticeInvolution.md)
