# Reflections

## Abstract

Actual charged residue comparison.

**Theorem 1.1 (Double coordinate reflection).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/Reflections.transformedCollisionKernel_double_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/Reflections.transformedCollisionKernel_double_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For an arbitrary oscillator polynomial and actual ground vector, reflecting both charges multiplies the actual transformed collision kernel by (-1)^(gamma+delta). Odd oscillator frequencies preserve translated support and attach its exact coefficient character. Even lattice norms cancel that character with the creation character. The actual ground actions are unchanged.

**Theorem 1.2 (All four reflected kernels on one actual diagonal).**

Lean statement: `D5/S3/VertexAlgebra/ChargedResidue/Reflections.charged_reflected_collision_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/ChargedResidue/Reflections.charged_reflected_collision_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Both matching lift equations reduce the four projected kernels to half the sum of the unreflected kernel and its signed right reflection. The latter contributes (-1)^v on the common creation diagonal. This gives precisely the two-pole weights, with each negative collision degree tested separately and with the original chargeScalar and ordered ground-action factors.

## References

- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/Reflections.charged_reflected_collision_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/ChargedResidue/Reflections.transformedCollisionKernel_double_reflection`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/SupportedResidue](SupportedResidue.md)
