# Cyclic invariance of the labeled coefficient

## Abstract

Cyclic invariance of the labeled coefficient.

**Theorem 1.1 (Cyclic invariance of the labeled coefficient).**

Lean statement: `D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingRotation.bounded_coefficient_rotation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingRotation.bounded_coefficient_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original lattice D with positive-definite real Gram matrix, every current-label function i : Fin 4 → Fin D.rank and every natural grade quadruple n, boundedFourCurrentCoefficient D hD i n equals boundedFourCurrentCoefficient D hD (rotateFour i) (rotateFour n). The rotation permutes all ten labeled matchings, their edge assignments, arc sides and independent winding coordinates bijectively.

The module retains the original constant-grade matching proof, cyclic edge and side equivalences, signed Gram symmetry and exact bounded finite residual, division and geometric sums. Rotation preserves the minimum and maximum grade and the complete charge cutoff. These results are consumed by the root energy-channel reduction and final all-grade endpoint. The finite identity makes no thermal convergence, annular, modular, sewing or physical-realization claim.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingRotation.bounded_coefficient_rotation`
- Dependency: [D5/S3/VertexAlgebra/Characters/FourCurrent/MatchingModes](MatchingModes.md)
