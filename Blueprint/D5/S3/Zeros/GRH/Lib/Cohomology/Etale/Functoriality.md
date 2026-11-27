# Functoriality

## Abstract

Functoriality

Functoriality of Ext of abelian presheaves in both variables and along exact functors.

**Theorem 1.1 (dimension_shift_induction).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Functoriality.dimension_shift_induction`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Functoriality.dimension_shift_induction` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Induction on Ext classes out of N: a property holds for every class if it holds for morphisms N → F and, for each short exact 0 → S₁ → S₂ → S₃ → 0, passes from x in Ext^n(N,S₃) to its image in Ext^{n+1}(N,S₁).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Functoriality.dimension_shift_induction`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Etale/Defs](Defs.md)
