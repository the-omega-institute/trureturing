# Char Of Det

## Abstract

Char Of Det

Tame Hecke character on determinants of integral adelic points is product of residue characters.

**Theorem 1.1 (apply_det_eq_prod).**

Lean statement: `D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharOfDet.apply_det_eq_prod`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharOfDet.apply_det_eq_prod` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let μ have weight e and tame part ψ, trivial outside finitely many distinct places w_i. For k in the stabiliser K₀ of the standard lattice, μ(det k) = ∏_i ψ_{w_i}(det(k mod w_i)).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/CharOfDet.apply_det_eq_prod`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/HeckeCharacter/LineParabolic](LineParabolic.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairReal](../../Weil/DualPair/PairReal.md)
