# Local eigenbasis blocks

## Abstract

A local eigenbasis change exposes positive classical blocks with the exact marginal eigenvalue weights.

**Definition 1.1 (A local change of coordinates).**

Lean statement: `D5/S3/Quantum/Subentropy/EigenbasisBlocks.localConjugate`

*Formalization.* `D5/S3/Quantum/Subentropy/EigenbasisBlocks.localConjugate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For matrices U on A and M on A×B, localConjugate U M is (U-adjoint tensor I) M (U tensor I). The first factor changes the coordinates on A and the second factor acts as the identity on B. This matrix is consumed by eigenbasis_blocks and the subadditivity proof.

**Theorem 1.2 (Positive blocks and their marginal weights).**

Lean statement: `D5/S3/Quantum/Subentropy/EigenbasisBlocks.eigenbasis_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Subentropy/EigenbasisBlocks.eigenbasis_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be any positive semidefinite matrix on A×B. Choose the eigenvector unitary U of partialTraceRight M, set K=localConjugate U M and define Y_x as K's diagonal B block at x. Then K is positive semidefinite, tr K=tr M, every Y_x is positive semidefinite, Σ_x Y_x=partialTraceLeft M, and tr Y_x is the corresponding real eigenvalue of partialTraceRight M. Block pinching of K has precisely these diagonal blocks and zero off-diagonal blocks.

The entry identity expands the Kronecker products and matrix products. Tracing over B transports the first marginal by U-adjoint and U. Tracing over A instead gives the cyclic trace of U-adjoint S U for each fixed B entry, so unitarity preserves the opposite marginal. Positivity follows from conjugation and principal submatrices. The diagonalized first marginal gives the block traces. Zero blocks and repeated marginal eigenvalues require no division or choice of normalized conditional states.

## References

- Truth anchor: `D5/S3/Quantum/Subentropy/EigenbasisBlocks.eigenbasis_blocks`
- Truth anchor: `D5/S3/Quantum/Subentropy/EigenbasisBlocks.localConjugate`
- Dependency: [D5/S3/Quantum/Subentropy/ClassicalQuantumGram](ClassicalQuantumGram.md)
