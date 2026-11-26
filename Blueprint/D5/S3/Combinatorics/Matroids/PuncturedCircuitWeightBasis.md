# Weight Directions for a Punctured Core

## Abstract

An integral basis adapted to the omitted basis.

**Theorem 1.1 (An integral basis for the two blocks).**

Lean statement: `D5/S3/Combinatorics/Matroids/PuncturedCircuitWeightBasis.exists_punctured_weight_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PuncturedCircuitWeightBasis.exists_punctured_weight_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep the pivot and choose a basis separately inside the omitted set with the pivot removed and outside the omitted set. The weights in each block lie on one basis vector with scalar the gcd of that block's weights. The alternating coefficient in the omitted block vanishes in the original basis exactly when it vanishes in the new basis.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PuncturedCircuitWeightBasis.exists_punctured_weight_basis`
- Dependency: [D5/S3/Combinatorics/Matroids/UniformCircuitBasis](UniformCircuitBasis.md)
