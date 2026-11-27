# Point Class

## Abstract

Point Class

Class of a rational point in Hodge cohomology; independence of choices, excision, sums.

**Theorem 1.1 (map_eq_sum_pointClass).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/PointClass.map_eq_sum_pointClass`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/PointClass.map_eq_sum_pointClass` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let X be separated, s a finite set of k-points, U = X∖s. If ξ ∈ Hdg^d(X, U) has local multiplicity n(z) ∈ k at each z ∈ s (IsPointSum), its image in Hdg^d(X) is Σ_{z∈s} n(z)·cl(z).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/PointClass.map_eq_sum_pointClass`
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/GrothendieckSymbol](GrothendieckSymbol.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Cohomology/WoodsHole/IsolatedCoincidences](../WoodsHole/IsolatedCoincidences.md)
