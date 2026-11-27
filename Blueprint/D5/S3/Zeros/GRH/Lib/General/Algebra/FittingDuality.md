# Fitting Duality

## Abstract

Fitting Duality

Relative lengths, kernels and determinants over a DVR; functions cut by matrix relations. Elementary bounds for relative lengths of Z_p-submodules: additivity, torsion layers, generators. Fitting ideals: base change, one more relation, iterated along a triangular family. Duality over O/p; dividing by a finite-length submodule costs its length in Fitting ideals.

**Theorem 1.1 (exists_cost_le_relLength).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Algebra/FittingDuality.exists_cost_le_relLength`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Algebra/FittingDuality.exists_cost_le_relLength` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let p ≠ 0, pΦ(O^n) ⊆ N, V a module of functions G → O/p. Some K ⊇ N contains Φ(v) whenever all linear Ψ with Ψ∘z ∈ V kill v, and some c ∈ O multiplies Fitt K into Fitt N, v(c) ≤ length of formsMod modulo V.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Algebra/FittingDuality.exists_cost_le_relLength`
- Dependency: [D5/S3/Zeros/GRH/Lib/Adelic/Witt/FrameAction](../../Adelic/Witt/FrameAction.md)
