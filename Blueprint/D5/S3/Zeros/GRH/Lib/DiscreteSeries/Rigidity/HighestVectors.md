# Highest Vectors

## Abstract

Highest Vectors

Highest weight vectors exist; filtration steps are spanned by lowering words, finite-dimensional.

**Theorem 1.1 (filtration_le_of_word_mem).**

Lean statement: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/HighestVectors.filtration_le_of_word_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/HighestVectors.filtration_le_of_word_mem` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let l have distinct entries and x be K-highest. A subspace that is stable under the compact lowering operators and contains all words of length ≤ s in the E_ab applied to x contains M_s, where M_0 = U(𝔨)x, M_{s+1} = M_s + 𝔤M_s.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/HighestVectors.filtration_le_of_word_mem`
- Dependency: [D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/CasimirBound](CasimirBound.md)
- Dependency: [D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/CommonEigenvectors](../../General/LinearAlgebra/CommonEigenvectors.md)
