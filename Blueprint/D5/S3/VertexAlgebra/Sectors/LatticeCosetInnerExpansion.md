# Native compressed source recursion

## Abstract

LatticeCosetInnerExpansion

**Definition 1.1 (compressedField).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion.compressedField`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion.compressedField` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary original lattice D, arbitrary finite external rank, integral B, symmetric even-diagonal C, external integral source and target charges a,d and every original state u, compressedField is the literal native ambient Y of J(a,u), composed with the target injection J(d) and output projection P(a+d). Its coefficient at integer mode m is the existing compressed coefficient. Native statewise Laurent truncation supplies its vertex-operator bound; no new graded cutoff or ambient positivity is assumed.

**Theorem 1.2 (compressed_multiplication_recursion).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion.compressed_multiplication_recursion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion.compressed_multiplication_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive definite original D, arbitrary finite external rank, integral B, symmetric even-diagonal C, integral external charges a,d, old oscillator index x, old integral source charge n and arbitrary old source polynomial f, the compressedField of single(n,X(x) f) equals normalMinusOne of the x-th divided derivative of the native integral shifted current in target sector d and compressedField of single(n,f). All original epsilon factors and integral zero-mode exponents remain in the compressedField. Negative current modes are independent of the external sector. Projection commutes with the negative modes, and injection transports every target current mode. Mapping the two native finite normal-product sums proves the equality. The finite coefficient arguments of LatticeCosetOperatorCorrection consume this recursion in the all-source inner creation expansion.

The source recurrence is the native lattice field recurrence of Bakalov-Kac, math/0402315v1, section 4.1. No occurrence-list independence, PBW reconstruction or new vertex algebra is assumed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion.compressedField`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeCosetInnerExpansion.compressed_multiplication_recursion`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeCosetCreationSeparation](LatticeCosetCreationSeparation.md)
