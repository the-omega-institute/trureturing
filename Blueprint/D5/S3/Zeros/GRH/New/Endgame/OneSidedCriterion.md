# One Sided Criterion

## Abstract

One Sided Criterion

One-sided bound gives a zero-free half-plane; small value in every long window.

**Theorem 1.1 (exists_window_sub_mul_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Endgame/OneSidedCriterion.exists_window_sub_mul_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Endgame/OneSidedCriterion.exists_window_sub_mul_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

If E and E' are polar (IsPolar), then for all large t and every X in [0, e^t] there is u in [t, t²] with E(u) − X E'(u) ≤ e^{−t}.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Endgame/OneSidedCriterion.exists_window_sub_mul_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/Analytic/QuadraticTwist/ZeroFreeTwist](../../Lib/Analytic/QuadraticTwist/ZeroFreeTwist.md)
- Dependency: [D5/S3/Zeros/GRH/New/Endgame/PrimeError](PrimeError.md)
