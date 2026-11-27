# Subgroup Integral

## Abstract

Subgroup Integral

Quotient measure defined by a cutoff weight of mass one on each orbit. Haar integrals over subgroups: translation, character orthogonality, sums over finite quotients.

**Theorem 1.1 (setIntegral_char).**

Lean statement: `D5/S3/Zeros/GRH/Lib/General/Measure/SubgroupIntegral.setIntegral_char`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/General/Measure/SubgroupIntegral.setIntegral_char` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Orthogonality of characters: let ν be a translation-invariant Borel measure on V, M an open subgroup, and χ(x+y) = χ(x)χ(y) for all x, y in V. Then ∫_M χ dν is ν(M) (read as 0 if infinite) if χ = 1 on M, and 0 otherwise.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/General/Measure/SubgroupIntegral.setIntegral_char`
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartialDerivComm](../LinearAlgebra/PartialDerivComm.md)
