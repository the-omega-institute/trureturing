# Trace Formula

## Abstract

Trace Formula

Trace of a (twisted) Hecke operator on algebraic forms as sum over representatives.

**Theorem 1.1 (trace_eq_weighted_sum).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/TraceFormula.trace_eq_weighted_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/TraceFormula.trace_eq_weighted_sum` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Trace formula. M: the F : G → W with F(e(γ)g) = ρ(γ)F(g), right K-invariant, zero on D. The sets {γ : e(γ)r_iK = gK} are finite, empty for g ∈ D, with ∑_i w_i·cardinality = 1 for g ∉ D; σ⁻¹K = K; TF = a·(s∘F∘σ⁻¹), a ∈ A[G] acting by right translation. Then dim M < ∞, tr T = ∑_i w_i ∑_γ φ(r_i⁻¹σ(e(γ)r_i)) tr(sρ(γ)), φ the image of a in A[G/K].

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/TraceFormula.trace_eq_weighted_sum`
- Dependency: [D5/S3/Zeros/GRH/Lib/Shimura/HeckeTower/GroupRingOperators](../HeckeTower/GroupRingOperators.md)
