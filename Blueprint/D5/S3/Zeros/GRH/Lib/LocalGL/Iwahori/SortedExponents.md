# Sorted Exponents

## Abstract

Sorted Exponents

Exchanging and sorting the θ_i(ϖ) of exponents (torusChar θ, l); eigenvectors give exponents in unitary representations.

**Theorem 1.1 (exists_sorted_of_type).**

Lean statement: `D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/SortedExponents.exists_sorted_of_type`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/SortedExponents.exists_sorted_of_type` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let ρ be unitary, x ≠ 0 and τ as in IsExponent.exists_sorted, V_x the span of the translates of x, with finite-dimensional I₁-fixed part. Some exponent (θ, l) has l(x) ≠ 0 and θ_i = τ_i on units, and V_x holds an eigenvector for θ∘σ with |θ_{σ(i)}(ϖ)| non-increasing.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/SortedExponents.exists_sorted_of_type`
- Dependency: [D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/IwahoriInjective](IwahoriInjective.md)
