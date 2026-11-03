# Actual Petz core trace stability

## Abstract

Actual Petz core trace stability.

**Theorem 1.1 (Schwarz and trace control the actual core error).**

Lean statement: `D5/S3/Quantum/Recovery/PetzCoreTraceStability.petz_core_traceNorm_le_four_physical_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzCoreTraceStability.petz_core_traceNorm_le_four_physical_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual supported model, let W be the spectral inverse square root of Q, H=sqrt(S), Y=W sqrt(T), C=H Psi(Y) P_R, and N=H Psi(W T W) H. The common Schwarz and trace supplier gives C C* <= N and Tr(N)=Tr(R)=1. Therefore ||N-R||_1 <= 4 ||E_M(B^(-1/2) eta)||_HS. P_R is retained in C; no unsupported full-space column equality or faithful-state hypothesis is used. The weighted estimate below consumes this bridge.

**Theorem 1.2 (The actual trace error is bounded by the weighted L2 error).**

Lean statement: `D5/S3/Quantum/Recovery/PetzCoreTraceStability.petz_core_traceNorm_le_weighted_inverse_sqrt_error`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzCoreTraceStability.petz_core_traceNorm_le_weighted_inverse_sqrt_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume L>=0 and s_j/r_i<=L on every positive input modular support pair. With d=A^(-1/2) xi-V B^(-1/2) eta, the actual core satisfies ||N-R||_1 <= 4 sqrt(L) sqrt(Re(sum_(j,i) conjugate(d_(j,i)) d_(j,i))). The last square root is the Euclidean L2 norm, not the supremum norm of a coordinate function. Combining this bound with the inverse-square-root entropy-loss estimate under m>0 and mI<=A,B gives (16/pi) sqrt(L/m) Delta^(1/4) for the fixed-reference Petz trace-stability proof. Output support annihilates that fixed channel completion on Phi(rho); no independent recovery channel is chosen from rho. This auxiliary composition makes no claim of literature novelty.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzCoreTraceStability.petz_core_traceNorm_le_four_physical_hs`
- Truth anchor: `D5/S3/Quantum/Recovery/PetzCoreTraceStability.petz_core_traceNorm_le_weighted_inverse_sqrt_error`
- Dependency: [D5/S3/Quantum/Recovery/PetzPhysicalWeightedCoordinates](PetzPhysicalWeightedCoordinates.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzSchwarzRecovery](PetzSchwarzRecovery.md)
