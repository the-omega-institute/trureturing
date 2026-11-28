# Trace Comparison

## Abstract

Trace Comparison

Equal Hecke traces on unitary groups differing at real places; Selberg principle.

**Theorem 1.1 (exists_trace_eq).**

Lean statement: `D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/TraceComparison.exists_trace_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/TraceComparison.exists_trace_eq` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let E contain μ_5040, with evenly many infinite places; K a level; each point of hK have irreducible characteristic polynomial at some finite place; B ≥ 16[E:ℚ](n+1)³, H ≥ 500n³+10n⁵. Then ∑⟨b_i, hb_i⟩, b an orthonormal basis of K-fixed forms of type e_l, is the same for all s, V with e_l a cusp kernel of order B, l of gap H.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/TraceComparison.exists_trace_eq`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/ReproducingKernel](../../Adelic/CuspForms/ReproducingKernel.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/FormalDegree](../../DiscreteSeries/Character/FormalDegree.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/ChangingSigns](ChangingSigns.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Weil/Periods/FiniteBesselGroup](../../Weil/Periods/FiniteBesselGroup.md)
