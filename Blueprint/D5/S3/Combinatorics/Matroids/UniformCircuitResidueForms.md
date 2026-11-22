# Uniform Circuit Residue Forms

## Abstract

Splitting simultaneous exterior equations.

**Theorem 1.1 (Splitting simultaneous exterior equations).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.closed_horizontal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.closed_horizontal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a covector a, a pivot x with a(x) = 1, and an insertion vector y, a form f is annihilated by covector multiplication and by insertion of y exactly when it is the covector product of a form g. The form g must vanish on insertion of either x or y and be killed by the scalar a(y). Insertion of x into f recovers g.

**Theorem 1.2 (The signed deletion coordinates).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.basis_covectorWedge_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.basis_covectorWedge_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Evaluating the covector product on an increasing basis tuple sums over its possible deletions, with each term multiplied by the deletion sign and the covector on the deleted vector.

**Theorem 1.3 (The weighted insertion coordinates).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.curryLeft_weighted_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.curryLeft_weighted_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inserting a sum of basis vectors with natural number weights gives the signed sum of the enlarged subset coordinates, with each term multiplied by its weight. Coefficients outside the degree of the form are taken to be zero.

**Theorem 1.4 (Insertion of a single basis vector).**

Lean statement: `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.curryLeft_smul_basis_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.curryLeft_smul_basis_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inserting a scalar multiple of the specified basis vector annihilates a form exactly when that scalar kills every coefficient whose indexing subset contains the specified vector.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.basis_covectorWedge_apply`
- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.closed_horizontal_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.curryLeft_smul_basis_eq_zero_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/UniformCircuitResidueForms.curryLeft_weighted_basis`
- Dependency: [D5/S3/HomologicalAlgebra/OrderedFaceSign](../../HomologicalAlgebra/OrderedFaceSign.md)
