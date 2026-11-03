# The original physical state Lie algebra

## Abstract

The actual lattice state fields define the physical primary spaces and the exact quotient of weight one states by the image of the original translation operator.

**Theorem 1.1 (Exact representative bracket).**

For every lattice datum, inverse Gram matrix and actual weight one primary states, the quotient bracket represented by the zero mode is

$$[\lbrack a\rbrack,\lbrack b\rbrack]=\lbrack a_0b\rbrack.$$ 

*Formalization.* `D5/S3/VertexAlgebra/Physical/OriginalPhysicalLie.physicalBracket_mk`.

**Theorem 1.2 (Lie structure).**

The quotient is an actual `LieRing` and `LieAlgebra ℂ`; skew symmetry is descended through the finite original skew primitive in the exact image of translation, and Jacobi is the zero-mode commutator identity.

*Formalization.* `D5/S3/VertexAlgebra/Physical/OriginalPhysicalLie.physicalBracket` and its native instances.

*Source.* Repository-derived from the actual lattice field, Ward, derivative, skew-symmetry, Virasoro and local-nilpotence sources.

The quotient is exactly `P^1 / T(P^0)`. The physical primary condition is the actual `L_0` eigenvalue together with annihilation by every positive original Virasoro mode. No positivity, critical rank, cutoff carrier, or BRST identification is used here.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Physical/OriginalPhysicalLie.physicalBracket_mk`
- Dependency: [LatticeActualConformalEnergy](../LatticeActualConformalEnergy.md)
- Dependency: [LatticeActualConformalWard](../LatticeActualConformalWard.md)
