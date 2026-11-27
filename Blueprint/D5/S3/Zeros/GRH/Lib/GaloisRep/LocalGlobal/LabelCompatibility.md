# Label Compatibility

## Abstract

Label Compatibility

Compatibility on inertia for squarefree depth-zero types induced with characters of the determinant.

**Theorem 1.1 (isLabelledAt).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LabelCompatibility.isLabelledAt`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LabelCompatibility.isLabelledAt` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let r be attached to an eigenform f (standard space, Weil data) with label c, χ_l, t_l at split w, T injective. Above w, r has finite type, the jumps of κ, and IsLabelledAt holds for c∏(X − x_{χ_l})^{t_l}, with determinants away from ℓ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LabelCompatibility.isLabelledAt`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLabel](../BaseChange/BaseChangeLabel.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/EigencharCompatibility](EigencharCompatibility.md)
