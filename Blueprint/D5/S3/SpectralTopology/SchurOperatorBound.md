# Finite Schur operator bound

## Abstract

A finite rectangular matrix has an L2 operator bound from its absolute row and column sums.

**Theorem 1.1 (Row and column bounds control the Euclidean operator).**

Lean statement: `D5/S3/SpectralTopology/SchurOperatorBound.l2_opNorm_le_schur`

*Proof.* Machine-checked in Lean as `D5/S3/SpectralTopology/SchurOperatorBound.l2_opNorm_le_schur` (`✓ std3`). ∎

*Citation.* Jue Xu and LeanPool contributors (2026). *Finite rectangular Schur operator bound*. URL: <https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/LowWeightPauliDynamics/SchurCore.lean>.

*Commentary.*

For every RCLike field K, finite row type I and finite column type J, with decidable equality on J, let A be an I by J matrix over K. If real R,C are nonnegative, every sum over j in J of the norm of A(i,j) is at most R, and every sum over i in I is at most C, then the Euclidean operator norm of A is at most sqrt(R*C). Empty row or column types are included. The norm is explicitly Matrix.Norms.L2Operator. Weighted Cauchy–Schwarz first bounds the squared action of each row, and summation uses the column bounds. The theorem is a minimal licensed port of Jue Xu's proof and is consumed by the actual Apollonian late adjacency estimate.

## References

- Truth anchor: `D5/S3/SpectralTopology/SchurOperatorBound.l2_opNorm_le_schur`
