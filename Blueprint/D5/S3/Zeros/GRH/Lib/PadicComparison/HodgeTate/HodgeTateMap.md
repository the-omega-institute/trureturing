# Hodge Tate Map

## Abstract

Hodge Tate Map

Hodge–Tate map in weight h: definition, naturality, scaling, multiplicativity.

**Theorem 1.1 (hodgeTateMap_cup).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateMap.hodgeTateMap_cup`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateMap.hodgeTateMap_cup` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Product formula: for Hodge classes x of degree a and y, λ_l(x × y) = ∑_{h ≤ l} C(l,h)(−1)^{(a+h)(l−h)} λ_h(x) × λ_{l−h}(y).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTateMap.hodgeTateMap_cup`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/HodgeTatePairs](HodgeTatePairs.md)
