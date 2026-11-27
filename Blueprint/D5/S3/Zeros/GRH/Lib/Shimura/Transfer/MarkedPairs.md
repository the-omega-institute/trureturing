# Marked Pairs

## Abstract

Marked Pairs

Conjugation invariance of the count; reflections commuting with a regular matrix.

**Theorem 1.1 (isReflection_eigenReflection).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Shimura/Transfer/MarkedPairs.isReflection_eigenReflection`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Shimura/Transfer/MarkedPairs.isReflection_eigenReflection` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let P = det(X − y) be separable, J_ν = eigenReflection True y ν. For roots μ of Φ_{v₀}P, J_μ is a reflection; each reflection J commuting with Φ_{v₀}(y) has a root μ: Φ_{v₀}(y)(J+1) = μ(J+1), and J = J_ν iff ν = μ.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Shimura/Transfer/MarkedPairs.isReflection_eigenReflection`
- Dependency: [D5/S3/Zeros/GRH/Lib/GaloisRep/Pseudocharacter/FibreSum](../../GaloisRep/Pseudocharacter/FibreSum.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/ChangingSigns](../../LocalGL/TraceFormula/ChangingSigns.md)
