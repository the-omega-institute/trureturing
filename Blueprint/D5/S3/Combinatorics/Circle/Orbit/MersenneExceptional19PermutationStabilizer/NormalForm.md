# Integral physical NormalForm

## Abstract

Integral physical exceptional19 NormalForm.

**Theorem 1.1 (triple equations).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm.triple_equations`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm.triple_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four actual triple indicators give the low and high block equations. Consecutive G, F and H carry equations give doubling in the interior. The geometric prefix sum is proved by induction; the retained rational normal form is separate from the integral normal form consumed below.

**Theorem 1.2 (geom sum).**

Lean statement: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm.geom_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm.geom_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four actual triple indicators give the low and high block equations. Consecutive G, F and H carry equations give doubling in the interior. The geometric prefix sum is proved by induction; the retained rational normal form is separate from the integral normal form consumed below.

This module supplies the consumed physical binary, carry and zero-mask identities for the all-r selected integral basis. The coordinates remain the original Fin(3d); scalar divisions occur only in integers.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm.geom_sum`
- Truth anchor: `D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/NormalForm.triple_equations`
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/Binary](Binary.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19PermutationStabilizer/CarryRows](CarryRows.md)
- Dependency: [D5/S3/Combinatorics/Circle/Orbit/MersenneExceptional19Stabilizer](../MersenneExceptional19Stabilizer.md)
