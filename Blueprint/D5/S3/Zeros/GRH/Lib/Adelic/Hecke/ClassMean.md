# Class Mean

## Abstract

Class Mean

Integral over double cosets as automorphism-weighted class sum; level change; smooth vectors.

**Theorem 1.1 (classIntegral_sum).**

Lean statement: `D5/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassMean.classIntegral_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassMean.classIntegral_sum` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Assume HasFiniteType for Γ and K. If F(g) = ∑_{i∈s} L_i(f_i(g a_i)) for all g, with L_i additive, a_i ∈ G and f_i smooth and left Γ-invariant, then the integral of F over Γ\G is ∑_{i∈s} L_i(integral of f_i).

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/Adelic/Hecke/ClassMean.classIntegral_sum`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/Measure/SubgroupIntegral](../../General/Measure/SubgroupIntegral.md)
