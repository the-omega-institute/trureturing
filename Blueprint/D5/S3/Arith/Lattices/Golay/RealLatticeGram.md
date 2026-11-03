# Integral Gram data from a positive even selfdual real lattice

## Abstract

Integral Gram data from a positive even selfdual real lattice

**Theorem 1.1 (The dual basis produces an integer inverse).**

Lean statement: `D5/S3/Arith/Lattices/Golay/RealLatticeGram.selfdual_span_gram_isUnit_det`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/RealLatticeGram.selfdual_span_gram_isUnit_det` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nondegenerate symmetric bilinear form and a selfdual integer basis span yield an integral inverse of the integral Gram matrix. The integer coordinates of the bilinear dual basis give a right inverse, so its determinant is a unit. No determinant value is assumed.

**Theorem 1.2 (A real lattice becomes actual integral charge data).**

Lean statement: `D5/S3/Arith/Lattices/Golay/RealLatticeGram.exists_latticeData_of_real_selfdual`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/Golay/RealLatticeGram.exists_latticeData_of_real_selfdual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a discrete full real lattice with a positive definite symmetric form, selfduality and even norms, the native integer basis extends over the reals. Its integral Gram matrix is positive definite and even, with unit determinant. The supplied integer charge linear equivalence is the actual basis map into the same real lattice, and it preserves every pairing.

## References

- Truth anchor: `D5/S3/Arith/Lattices/Golay/RealLatticeGram.exists_latticeData_of_real_selfdual`
- Truth anchor: `D5/S3/Arith/Lattices/Golay/RealLatticeGram.selfdual_span_gram_isUnit_det`
- Dependency: [D5/S3/VertexAlgebra/LatticeGeneratingFieldLocality](../../../VertexAlgebra/LatticeGeneratingFieldLocality.md)
