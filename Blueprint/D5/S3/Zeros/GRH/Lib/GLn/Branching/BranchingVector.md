# Branching Vector

## Abstract

Branching Vector

Norm on Weyl's lattice, Zariski density of U(n), hook number clears denominators. Cartan multiplication: integral, isometric, equivariant, split; submultiplicativity of norms. Denominator of the branching vector bounded by the columns of height at least q.

**Theorem 1.1 (exists_smul_weylKernel_mul_eq_toPoly).**

Lean statement: `D5/S3/Zeros/GRH/Lib/GLn/Branching/BranchingVector.exists_smul_weylKernel_mul_eq_toPoly`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/GLn/Branching/BranchingVector.exists_smul_weylKernel_mul_eq_toPoly` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let κ₀(h) = κ'(h)+γ(h) for 0<h<|n_τ|, κ'(i) = 0 for i<q, and f number the rows with rowPos ≤ f+1. Some integer c>0, at most L^{3L} whenever L ≥ ∑_τ∑_{q≤h<|n_τ|} hκ₀(h), and integer vector η satisfy c·K_γ·K_{κ'} = toPoly η, kernels weylKernel at the permutation arrays of f and rowPos.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/GLn/Branching/BranchingVector.exists_smul_weylKernel_mul_eq_toPoly`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Witt/FrameAction](../../Adelic/Witt/FrameAction.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Gram](../SchurModule/Gram.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/SubmersionZero](../../General/LinearAlgebra/SubmersionZero.md)
