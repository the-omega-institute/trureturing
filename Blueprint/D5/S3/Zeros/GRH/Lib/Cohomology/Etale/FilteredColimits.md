# Filtered Colimits

## Abstract

Filtered Colimits

Commutation of cohomology with filtered limits descends along Čech covers.

**Theorem 1.1 (of_cech).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/FilteredColimits.of_cech`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/FilteredColimits.of_cech` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Take a cone over a cofiltered system of covers E_j → Y_j whose vertex is a cover. If ContinuousUpTo holds at level r+1 for the E_j and at level r for all fibre powers with at least one factor, it holds at level r+1 for the Y_j.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/Etale/FilteredColimits.of_cech`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Algebra/CechDescent](../../General/Algebra/CechDescent.md)
