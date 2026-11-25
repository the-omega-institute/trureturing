# Rational rank two for diagonal Fibonacci marginals

## Abstract

Two Gaussian norm equations for rational rank two with diagonal edge blocks.

**Theorem 1.1 (The coupling norm and the determinant norm).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibDiagonalRank.rational_rank_le_two_diagonal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibDiagonalRank.rational_rank_le_two_diagonal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let b be a positive rational middle occupation and put t = 1 − b. Set the observed couplings to zero and take diagonal endpoint blocks with entries (l, t − l) and (r, t − r), where l and r are distinct nonnegative rationals. There is a trace-one positive semidefinite joint extension with rational coordinates and rank at most two exactly when b(t − l − r) and lr are both Gaussian norms.

For coupling z, Schur elimination subtracts |z|²/b from the occupied entry of each block. The difference of the two residual determinants is (l − r)(t − l − r − |z|²/b). Equality fixes |z|² and leaves the two nonnegative diagonal residuals (l, r) and (r, l). Their common determinant is lr, which is the second norm in the fixed-coupling criterion.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibDiagonalRank.rational_rank_le_two_diagonal_iff`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibCoherentRank](FibCoherentRank.md)
