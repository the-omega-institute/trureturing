# Size Estimates

## Abstract

Size Estimates

Size bookkeeping: row lengths, factorial sizes, class counts, sum of allowed losses.

**Theorem 1.1 (sum_allowedLoss_mul_log_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Columns/SizeEstimates.sum_allowedLoss_mul_log_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Columns/SizeEstimates.sum_allowedLoss_mul_log_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For every finite set U of natural numbers, ∑_{p∈U} err(p) log p ≤ fa(log b)³, with err = Data.allowedLoss the allowed loss; the bound is Data.budget.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Columns/SizeEstimates.sum_allowedLoss_mul_log_le`
- Dependency: [D5/S3/Zeros/GRH/New/Columns/ColumnDefs](ColumnDefs.md)
- Dependency: [D5/S3/Zeros/GRH/New/Core/ClassCountBound](../Core/ClassCountBound.md)
