# Branching

## Abstract

Branching

Extremal vector is cyclic; Schur's lemma for U(n) on Weyl modules. Dual of a Weyl module by Jacobi complementary minors, as unimodular integral isometry. Multiplicity-one branching GL(n+1) to GL(n) as an integral map with explicit norm bound.

**Theorem 1.1 (exists_branching_matrix).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GLn/Branching/Branching.exists_branching_matrix`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GLn/Branching/Branching.exists_branching_matrix` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Branching from rank n+1 to n = |n_τ|: let κ = γ+κ', κ₀(h) = κ'(h)+γ(h+1) for 0<h<n, e₀ = e+κ'(n), κ'(i) = 0 for i<q. Some integer matrix br satisfies SpansBranchingMaps, br·ρ_{κ,e}(diag(g,s)) = ∏_τ s_τ^{e_τ+∑_{1≤h≤n}γ_τ(h)}·ρ_{κ₀,e₀}(g)·br over fields of characteristic 0, and ‖br‖ ≤ L^{3L} in Gram norms whenever L ≥ ∑_τ∑_{q≤h<n} hκ₀(h).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GLn/Branching/Branching.exists_branching_matrix`
- Dependency: [D5/S3/Zeros/GRH/Lib/GLn/Branching/BranchingVector](BranchingVector.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ExpSurjective](../../General/LinearAlgebra/ExpSurjective.md)
