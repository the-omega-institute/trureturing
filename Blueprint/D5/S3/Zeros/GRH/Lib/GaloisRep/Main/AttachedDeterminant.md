# Attached Determinant

## Abstract

Attached Determinant

Field cut out by χχ^c is CM of prime degree, with norm-detecting character. CM extension of prime degree with prescribed tame completion at a split place. Auxiliary quadratic CM extension containing imaginary quadratic field, split at given places. Local properties descend from the base-changed form's representation to the original one. Determinant of an attached Galois representation is the avatar of the twisted central character.

**Theorem 1.1 (exists_det_eq_avatar).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/Main/AttachedDeterminant.exists_det_eq_avatar`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/Main/AttachedDeterminant.exists_det_eq_avatar` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For r attached to a rank n eigenform f, det r is the avatar of an algebraic Hecke character θ of explicit type; at split w, θ_w gives eigenvalues of unit scalars on f, and (−1)^n Q(0) at uniformisers, Q a Hecke polynomial of f.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/Main/AttachedDeterminant.exists_det_eq_avatar`
- Dependency: [D5/S3/Zeros/GRH/Lib/ClassField/Grunwald/Grunwald](../../ClassField/Grunwald/Grunwald.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeEigenchar](../BaseChange/BaseChangeEigenchar.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicHodge/Characters/LocalCharacters](../../PadicHodge/Characters/LocalCharacters.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairSumNegation](../../Weil/DualPair/PairSumNegation.md)
