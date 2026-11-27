# Theta Lift

## Abstract

Theta Lift

Nonzero theta lift to larger rank; Hecke polynomials twisted and gaining a string.

**Theorem 1.1 (exists_theta_lift_heckePoly).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/EvenRank/ThetaLift.exists_theta_lift_heckePoly`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/EvenRank/ThetaLift.exists_theta_lift_heckePoly` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Theta lift: for f ≠ 0 of rank n ≥ 1, weight (κ, e), s > n, b unramified of weight c ≤ e, some F ≠ 0 of weight κ' on I_{n+s} is spherical where f is; its rescaled Hecke polynomial is P·∏_{l<s}(X − θ_l(ϖ)), with θ_l given by AutChar.HasWeight.toAlgebraic.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/EvenRank/ThetaLift.exists_theta_lift_heckePoly`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LocalTranslates](../LocalGlobal/LocalTranslates.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Tadic/ChainLemma](../../LocalGL/Tadic/ChainLemma.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/CompactLift/RallisFormula](../../Weil/CompactLift/RallisFormula.md)
