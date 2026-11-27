# Delta Forms

## Abstract

Delta Forms

Smooth vector-valued forms for a group pair and their right translation. Operator norm of a Schur functor bounded by powers of singular values. Algebraic modular forms: delta forms, values at class representatives, dimension at neat level.

**Theorem 1.1 (classSum_deltaForm).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/DeltaForms.classSum_deltaForm`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/DeltaForms.classSum_deltaForm` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let e be injective and HasFiniteType hold. If additive maps L(g): W → ℂ satisfy L(e(γ)xk)(χ(k)ρ(γ)v) = L(x)(v) for all γ, k, the class sum of g ↦ L(g)(δ(g)) is L(x)(v), where δ is deltaForm at x, v.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/DeltaForms.classSum_deltaForm`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassMean](../Hecke/ClassMean.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GLn/Branching/BranchingVector](../../GLn/Branching/BranchingVector.md)
