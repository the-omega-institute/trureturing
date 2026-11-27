# Row Ladder

## Abstract

Row Ladder

The one-square lemma applied to a grid square, constant costing one square.

**Theorem 1.1 (descent_past_gridPathMap).**

Lean statement: `D5/S3/Zeros/GRH/New/Exchange/RowLadder.descent_past_gridPathMap`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Exchange/RowLadder.descent_past_gridPathMap` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

A descent moves past a lifts. For a ≤ b < m there are κ and c(ϑ) ≠ 0 costing a squares such that, if each edge of w avoids grid z or is (i, b) → (i+1, b) with i ≥ a, every tidy Λ of order n has a tidy Φ of order n + 2a with Λ(path to (a, b)) = (κ/c(ϑ))·Φ(path to (a, b+1), then descent), under linear functionals reading only w.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Exchange/RowLadder.descent_past_gridPathMap`
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/CostOfSquares](CostOfSquares.md)
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/GridMove](GridMove.md)
- Dependency: [D5/S3/Zeros/GRH/New/Exchange/OneSquare](OneSquare.md)
