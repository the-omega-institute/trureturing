# Binary Elimination Preserving the Quadratic Half-Norm

## Abstract

Binary Elimination Preserving the Quadratic Half-Norm.

**Theorem 1.1 (Binary Elimination Preserving the Quadratic Half-Norm).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/BinarySchur.even_binary_elimination`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/BinarySchur.even_binary_elimination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H be the even binary Gram matrix with rows (2a,b) and (b,2c) over Z/8, and suppose b is odd. Let A have rows (a,b) and (0,c), so that A+A transpose=H. A general coupling to remaining coordinates is a matrix B, and L is the coefficient matrix of their half-norm.

Put T=H inverse times B, P=block(1,-T;0,1), and R=L-T transpose times A transpose times T. The substitution P has determinant one. It sends the symmetric Gram matrix block(H,B;B transpose,L+L transpose) to block(H,0;0,R+R transpose). Hence the residual symmetric even Gram matrix retains unit determinant when the whole Gram matrix has unit determinant.

The quadratic statement is stronger than the determinant statement. On each vector w, the half-norm given by block(A,B;0,L) at P*w equals the half-norm of A on the binary coordinates plus the half-norm of R on the remaining coordinates. The transformed off-diagonal coefficient blocks are negatives of each other after transpose, so their contributions cancel on the same vector.

The complement may have no coordinates. This is a binary elimination step over Z/8; a complete decomposition still requires selecting an odd pivot, reindexing the original Gram matrix, iterating the step, and proving compatibility of the quadratic reduction with the original mod-two charge cocycle. It does not assume a positive Gauss sign or choose a different actual ground representation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/BinarySchur.even_binary_elimination`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/BinaryGauss](BinaryGauss.md)
