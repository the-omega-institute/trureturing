# Actual marginal residual geometry

## Abstract

The actual AB and B marginals inherit the recovered residual. Every centered Hermitian test is approximately fixed by the reduced channel. Diagonalizing an attained nonzero test controls the physical flip terms and the complex off-diagonal block; small centered correlation gives an A-BC product repair.

**Theorem 1.1 (Right partial trace contracts Hermitian trace norm).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.partialTraceRight_contract`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.partialTraceRight_contract` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace norm of the right partial trace of a Hermitian matrix is no greater than the trace norm of the original matrix.

**Definition 1.2 (The right tensor algebra map).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.tensorRight`

*Formalization.* `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.tensorRight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tensoring a matrix on the left with the identity defines a complex star algebra map into matrices on the product coordinate type.

**Definition 1.3 (The channel with C discarded).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.reducedAction`

*Formalization.* `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.reducedAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the physical B to BC channel and then discard C, obtaining the actual reduced B action on matrices.

**Theorem 1.4 (Residual of the actual B marginal).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.actual_B_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.actual_B_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The trace norm difference between the actual B marginal and its reduced-channel image is at most twice the half trace distance between the original state and its actual recovered reference.

**Theorem 1.5 (Every centered test is approximately fixed).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.all_centered_tests_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.all_centered_tests_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian A contraction, its centered qubit slice has residual at most 4r under the actual reduced channel obtained by discarding C after T. The AB and B residuals each have trace norm at most 2r.

**Theorem 1.6 (An actual isometry in the attained eigenbasis).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.diagonalized_residual_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.diagonalized_residual_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonzero traceless Hermitian qubit K and any actual physical isometry W, diagonalize K and rotate the same input and output qubit coordinate. The resulting physical isometry V has the exact transported action on every complex matrix. If the K residual has trace norm at most e, both its total flip probability and the difference of its diagonal-to-coherence terms are at most e divided by twice the operator norm of K.

**Theorem 1.7 (Complex block duality from the same diagonal geometry).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.complex_block_bound_of_diagonal_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.complex_block_bound_of_diagonal_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the centered AB matrix, suppose every Hermitian contraction slice has operator norm at most x greater than zero and actual reduced-isometry residual at most 4r. If the total flip probability and coherence-coefficient difference are each at most 2r divided by x, then for positive retained-column gap g the complex off-diagonal block has trace norm at most 16r divided by g. The modulus trace pairing first has bound 8r divided by g, and complex duality retains its factor two.

**Theorem 1.8 (Actual residual geometry in the attained basis).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.actual_diagonal_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.actual_diagonal_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive attained centered slice norm x, diagonalization and coherent transport give an actual dilation of the transported channel. Every Hermitian contraction has residual at most 4r. The flip sum and coefficient difference are at most 2r divided by x; a positive phase-sensitive gap g bounds the complex off-diagonal centered block by 16r divided by g. The physical dilation is obtained by finite reindexing of the output coordinate, so arbitrary finite coordinate universes remain in scope.

**Theorem 1.9 (A product repair from small correlation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.product_repair_of_centered_correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.product_repair_of_centered_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an attaining reference test with slice operator norm x, the actual state a tensor T(b) on the same ABC space has ordinary conditional mutual information zero and lies within trace distance r plus 3x of rho. Here a and b are the actual marginals of P.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.actual_B_residual`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.actual_diagonal_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.all_centered_tests_residual`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.complex_block_bound_of_diagonal_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.diagonalized_residual_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.partialTraceRight_contract`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.product_repair_of_centered_correlation`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.reducedAction`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitActualResidualGeometry.tensorRight`
- Dependency: [D5/S3/Quantum/Recovery/QubitCenteredTransport](QubitCenteredTransport.md)
