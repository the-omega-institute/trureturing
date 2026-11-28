# Bad Share

## Abstract

Bad Share

The bound bad_share_le for the share of bad types. Primitive labels: stable under scaling of roots; norm of a generator generates. A primitive cuspidal character has a cubic twist agreeing off irreducible characteristic polynomials.

**Theorem 1.1 (bad_share_le).**

Lean statement: `D5/S3/Zeros/GRH/New/Trace/BadShare.bad_share_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Trace/BadShare.bad_share_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Bad share: take f fields of order q, 1 < r = |n| < q, M ≥ 1, (1+M+2r)/q ≤ ε ≤ 1, 2r(2r log q + 1)L ≤ f. For e the sum of tupleIdem over goodTuples M r, Re (1 − e)(1) ≤ fε + exp(−L).

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Trace/BadShare.bad_share_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Groups/CentralConvolution](../../Lib/General/Groups/CentralConvolution.md)
