# Steep Parameters

## Abstract

Steep Parameters

The chosen parameters satisfy the steepness hypothesis of the Laplace-method lemma.

**Theorem 1.1 (exists_isSteep).**

Lean statement: `D5/S3/Zeros/GRH/New/Exchange/SteepParameters.exists_isSteep`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/New/Exchange/SteepParameters.exists_isSteep` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For either grid z, one ordering e of the indices gives the signs and parameter of the node (0, 0), offset 0, the shape IsSteep with bound w₀(τ) = Data.w 0 τ at every infinite place τ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/New/Exchange/SteepParameters.exists_isSteep`
- Dependency: [D5/S3/Zeros/GRH/New/DiscreteSeries/RestrictionLemma](../DiscreteSeries/RestrictionLemma.md)
- Dependency: [D5/S3/Zeros/GRH/New/Trace/GoodIdempotent](../Trace/GoodIdempotent.md)
