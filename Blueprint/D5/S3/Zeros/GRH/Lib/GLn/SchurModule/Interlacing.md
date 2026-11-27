# Interlacing

## Abstract

Interlacing

Leading exponent in a row interlaces; leading coefficient is again semi-invariant.

**Theorem 1.1 (degree_rowExpansion_mem_interlacing).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Interlacing.degree_rowExpansion_mem_interlacing`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Interlacing.degree_rowExpansion_mem_interlacing` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Interlacing: for f in ∇ of weight l, the leading exponent γ of f in the variables of row x (order PolyRep.columnOrder; γ = 0 if f = 0) satisfies γ(i) ≤ l(c x, i) − l(c x, i+1), truncated at 0, for all i.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Interlacing.degree_rowExpansion_mem_interlacing`
- Dependency: [D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Bordering](Bordering.md)
