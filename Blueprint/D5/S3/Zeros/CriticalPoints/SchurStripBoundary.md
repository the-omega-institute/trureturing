# The right boundary and its equality phases

## Abstract

The sharp right boundary trace estimate records exactly the phase information required by equality.

**Theorem 1.1 (The right boundary bound with phase rigidity).**

Lean statement: `D5/S3/Zeros/CriticalPoints/SchurStripBoundary.right_boundary_bound_and_phases`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/CriticalPoints/SchurStripBoundary.right_boundary_bound_and_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n>0, p>0, positive t_j, unit phases u_j, every real y and every unitary matrix K, the norm of Tr(K H(n,p(1+iy)/2) diag(u_j positivePower(t_j,p(1+iy))) H(n,p(1+iy)/2)) is at most M=((n+1)^p+n−1)/n times sum_j t_j^p. If equality holds, then u_i exp(ipy log t_i)=u_j exp(ipy log t_j) for every i,j. The explicit Hermitian-power columns have equal squared norms and pairwise nonzero inner products.

## References

- Truth anchor: `D5/S3/Zeros/CriticalPoints/SchurStripBoundary.right_boundary_bound_and_phases`
- Dependency: [D5/S3/Zeros/CriticalPoints/RankOneComplexPowers](RankOneComplexPowers.md)
- Dependency: [D5/S3/Zeros/CriticalPoints/RankOneTraceBound](RankOneTraceBound.md)
