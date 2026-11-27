# Base Change Eigenchar

## Abstract

Base Change Eigenchar

Twisted trace over E' is proportional to trace over E for matching functions. Existence of weak prime-degree base change for definite unitary groups with matched local data. Base change keeps a pro-p Iwahori eigencharacter, composed with the norm.

**Theorem 1.1 (exists_baseChange_isIwahoriEigen).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeEigenchar.exists_baseChange_isIwahoriEigen`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeEigenchar.exists_baseChange_isIwahoriEigen` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Base change along a step E'/E with compatible CM types, at a split w with μ_w = 1 and one split place u above: if f has eigencharacter ξ at w, some eigenform f' over E' matches f off w (IsWeakBaseChange) with eigencharacter ξ∘Nm at u.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeEigenchar.exists_baseChange_isIwahoriEigen`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLevel](BaseChangeLevel.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/ParahoricColumns](ParahoricColumns.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/WeilDataExtension](WeilDataExtension.md)
