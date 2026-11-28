# Label Uniqueness

## Abstract

Label Uniqueness

Given an injective lift to forms on a definite group, a Hecke eigensystem has at most one primitive label at a chosen place over g.

**Theorem 1.1 (occurringLabels_subsingleton).**

Lean statement: `D5/S3/Zeros/GRH/New/GaloisRep/LabelUniqueness.occurringLabels_subsingleton`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/GaloisRep/LabelUniqueness.occurringLabels_subsingleton` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let L inject level g forms on V into definite algebraic forms, make the p-part spherical with fixed eigenvalues at split places off g, and intertwine the parabolic action at x up to ψ∘det and distinct χ_l∘det, of orders dividing Mω. Then Data.occurringLabels V p x has at most one element.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/GaloisRep/LabelUniqueness.occurringLabels_subsingleton`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/LabelCompatibility](../../Lib/GaloisRep/LocalGlobal/LabelCompatibility.md)
- Dependency: [D5/S3/Zeros/GRH/New/Selmer/LevelPlacesChosen](../Selmer/LevelPlacesChosen.md)
