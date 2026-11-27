# Tail Bounds

## Abstract

Tail Bounds

Explicit Lipschitz bound for the coefficient; crude bound for degree times tail integrals.

**Theorem 1.1 (integral_tail_le).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/TailBounds.integral_tail_le`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/TailBounds.integral_tail_le` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

For l=2λ of gap 500n³+B with all |l_a| ≤ L and a natural number c > 8n², the function deg_λ·(2/‖g‖)^c is integrable on U(diag ε), with integral at most 8(2000(n+L+1)⁶)^{2n²}·2^c.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/TailBounds.integral_tail_le`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/CuspKernel/SchurOrthogonality](../CuspKernel/SchurOrthogonality.md)
