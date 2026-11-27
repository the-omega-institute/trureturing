# Average

## Abstract

Average

Localisation identity for Schur polynomials; extracting Schur weights by algebraic independence of embeddings. Means, inner product, characters, irreducible characters, group-algebra elements of a finite group. Elementary rules for means of complex functions over finite sets and groups.

**Theorem 1.1 (map_prod_rootCoeffEval_eq_zero).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Combinatorics/Average.map_prod_rootCoeffEval_eq_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Combinatorics/Average.map_prod_rootCoeffEval_eq_zero` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let the functions c(i, σ) be algebraically independent, |ι| ≥ total degree of q σ, and each multiset x j σ have a elements. A linear form killing the families j ↦ ∏_{i,σ} ∏_{t ∈ x j σ} (1 − c(i, σ)(α) t) for all α kills j ↦ ∏_σ rootCoeffEval(x j σ)(q σ).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Combinatorics/Average.map_prod_rootCoeffEval_eq_zero`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Analysis/OstrowskiTaussky](../Analysis/OstrowskiTaussky.md)
