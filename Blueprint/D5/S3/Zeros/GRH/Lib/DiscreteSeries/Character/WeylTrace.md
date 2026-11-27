# Weyl Trace

## Abstract

Weyl Trace

Weyl character formula at regular semisimple elements of products of GL_n.

**Theorem 1.1 (trace_weylRep).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/WeylTrace.trace_weylRep`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/WeylTrace.trace_weylRep` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Weyl's character formula: if each g_v in GL_a(ℂ) has distinct eigenvalues x_{v,i}, the trace of weylRep κ e at g times ∏_v det(x_{v,i}^j) equals ∏_v det(x_{v,i}^(e_v + λ_{v,a−1−j} + j)), with 0 ≤ i, j < a and λ the weight diagramWeight of κ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Character/WeylTrace.trace_weylRep`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/WeightParameter](../../Adelic/CuspForms/WeightParameter.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/DefiniteTrace](../../Shimura/TraceFormula/DefiniteTrace.md)
